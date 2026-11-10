"""Compare generated Alloy tests and their fault detection across runs.

Example:
    python analysis/compare_runs.py alloytools.jar run1.json run2.json -o overlap

The input files are read only. Reports are written to overlap.md and overlap.json.
"""

import argparse
from collections import Counter, defaultdict
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import sys

if __package__:
    from .analyze import generated_test_sources
    from .definitions import DefinitionChecker
    from .suite_metadata import complete_suite, requested_n
else:
    from analyze import generated_test_sources
    from definitions import DefinitionChecker
    from suite_metadata import complete_suite, requested_n


METHOD = (
    "Tests are grouped separately for each benchmark, requirement, and intended polarity. "
    "Only satisfiable tests with an explicit expect 0/1 and a unique visible structure "
    "modulo atom renaming are compared. Each structure is encoded as a complete instance "
    "predicate I; another test P matches when P and I is satisfiable under P's original "
    "scopes and integer bitwidth. Signatures, fields, and ordering successors are preserved; "
    "integer/string values retain their identities. Skolem witnesses and private module "
    "implementation relations are ignored. Different commands encoding the same structure "
    "count once in overlap sets. No larger comparison scope is introduced."
)

FAILURE_STAGES = ("syntax", "inconsistent", "nonunique", "previous", "oracle")
ASSESSMENT_ISSUES = ("solver_error", "unsupported")
FAILURE_METHOD = (
    "Validity is checked for every generated command independently of the structural comparison cohort. "
    "Commands are assigned their first failing stage: syntax, consistency, uniqueness, preceding "
    "requirement oracles, or target oracle. Counts include repeated command occurrences. "
    "Recurrence measures which requirements have at least one invalid test in each run; it does "
    "not establish that the same semantic misunderstanding occurred. Solver errors and unsupported "
    "encodings are unassessed, not confirmed invalid. Missing tests concern suite completeness "
    "and do not count as invalid commands."
)

DETECTION_METHOD = (
    "Fault detection is compared only for requirements with a complete valid suite in every run. "
    "Requested counts come from generation metadata or recognized filenames, never generated counts. "
    "All runs use the same erroneous-specification catalogue and preceding requirement oracles. "
    "A specification is detected if at least one test disagrees with its expect annotation when "
    "that specification replaces the target oracle. Tests retain their original scopes and bitwidth. "
    "Exact duplicate specifications are counted once; IDs hash the benchmark, requirement, and "
    "specification text with leading/trailing whitespace removed. Unparseable specifications and "
    "specifications with an unassessed outcome in any run are excluded from every run's denominator "
    "and reported separately, never counted as missed. Empty set unions have no defined Jaccard. "
    "Primary averages weight requirements equally; pooled statistics are also provided. "
    "Agreement establishes discrimination against this fault catalogue, not scenario equivalence."
)


class TestExclusion(Exception):
    def __init__(self, stage, reason):
        super().__init__(reason)
        self.stage = stage


@dataclass
class SolvedTest:
    world: object
    command: object
    predicate: str
    profile: tuple
    polarity: str


class AlloyComparator:
    def __init__(self, jar):
        import jpype
        import jpype.imports
        if not jpype.isJVMStarted():
            jpype.startJVM(classpath=[str(Path(jar).resolve())])
        from edu.mit.csail.sdg.parser import CompUtil
        from edu.mit.csail.sdg.translator import A4Options, TranslateAlloyToKodkod
        from kodkod.engine.satlab import SATFactory
        self.parser = CompUtil
        self.translator = TranslateAlloyToKodkod
        self.options = A4Options()
        self.options.solver = SATFactory.get("sat4j")
        self.models = {}
        self.match_queries = 0

    def execute(self, world, command):
        return self.translator.execute_command(
            None, world.getAllReachableSigs(), command, self.options)

    def model_checker(self, model):
        if model not in self.models:
            world = self.parser.parseEverything_fromString(None, model)
            # Alloy synthesizes a Default command with no source filename when
            # declarations contain no explicit command.
            if any(str(command.pos().filename) for command in world.getAllCommands()):
                raise ValueError("Benchmark declarations must not contain run/check commands.")
            self.models[model] = DefinitionChecker(world)
        return self.models[model]

    def profile(self, checker, world, solution):
        """Cheap isomorphism invariants; equality here does not establish a match."""
        signatures = {str(sig.label): sig for sig in world.getAllReachableSigs()}
        atoms = {str(row.atom(0)) for root in checker.roots
                 for row in solution.eval(signatures[root])}
        result = []
        for key, display in checker.required.items():
            if key[0] == "sig":
                expression, arity = signatures[key[1]], 1
            elif key[0] == "field":
                expression = next(f for f in signatures[key[1]].getFields()
                                  if str(f.label) == key[2])
                arity = int(expression.type().arity())
            else:
                expression = self.parser.parseOneExpression_fromString(world, display)
                arity = 2
            rows = list(solution.eval(expression))
            literals = Counter((column, str(row.atom(column))) for row in rows
                               for column in range(arity)
                               if str(row.atom(column)) not in atoms)
            result.append((key, arity, len(rows), tuple(sorted(literals.items()))))
        return tuple(sorted(result))

    def solve(self, model, source, on_stage=None):
        checker = self.model_checker(model)
        try:
            world = self.parser.parseEverything_fromString(None, model + "\n" + source)
            commands = world.getAllCommands()
            if len(commands) != 1 or commands[0].expects not in (0, 1):
                raise ValueError("A test must have one run command with explicit expect 0 or 1.")
            command = commands[0]
        except Exception as exc:
            raise TestExclusion("syntax", str(exc)) from exc
        if on_stage:
            on_stage("parsed")
        try:
            solution = self.execute(world, command)
        except Exception as exc:
            raise TestExclusion("solver_error", str(exc)) from exc
        if not solution.satisfiable():
            raise TestExclusion("inconsistent", "Unsatisfiable under the model declarations and command scopes.")
        if on_stage:
            on_stage("consistent")
        try:
            unique = checker.unique(world, command, solution, self.options)
            if not unique:
                raise TestExclusion("nonunique", "The test admits non-isomorphic satisfying instances.")
            predicate = checker.witness_predicate(world, solution)
            profile = self.profile(checker, world, solution)
        except TestExclusion:
            raise
        except ValueError as exc:
            raise TestExclusion("unsupported", str(exc)) from exc
        # Unexpected solver/encoding errors abort rather than yielding false differences.
        if on_stage:
            on_stage("unique")
        return SolvedTest(world, command, predicate, profile,
                          "positive" if command.expects == 1 else "negative")

    def require_valid(self, solved, previous_oracles, oracle):
        def with_oracles(oracles):
            formula = "{\n" + "\n".join("{\n" + value + "\n}" for value in oracles) + "\n}"
            expression = self.parser.parseOneExpression_fromString(solved.world, formula)
            return self.execute(solved.world, solved.command.change(
                solved.command.formula.and_(expression))).satisfiable()

        if previous_oracles and not with_oracles(previous_oracles):
            raise TestExclusion("previous", "Violates a preceding requirement oracle.")
        satisfies = with_oracles([*previous_oracles, oracle])
        if satisfies != (solved.polarity == "positive"):
            raise TestExclusion("oracle", "The intended polarity disagrees with the requirement oracle.")

    def matches(self, solved, predicate):
        if solved.predicate == predicate:
            return True
        expression = self.parser.parseOneExpression_fromString(solved.world, predicate)
        self.match_queries += 1
        return self.execute(solved.world, solved.command.change(
            solved.command.formula.and_(expression))).satisfiable()

    def detection_background(self, task):
        return task["model"] + "\n" + "\n".join(
            "fact {\n" + oracle + "\n}" for oracle in task["previous"])

    def validate_fault(self, task, specification):
        # Validate independently of generated command names so parseability
        # cannot change the shared catalogue from one run to another.
        try:
            self.parser.parseEverything_fromString(
                None, self.detection_background(task) + "\nfact {\n" + specification + "\n}")
        except Exception as exc:
            raise TestExclusion("syntax", str(exc)) from exc

    def prepare_detection_suite(self, task, sources):
        prepared = []
        for source in dict.fromkeys(sources):
            world = self.parser.parseEverything_fromString(
                None, self.detection_background(task) + "\n" + source)
            commands = world.getAllCommands()
            if len(commands) != 1 or commands[0].expects not in (0, 1):
                raise ValueError("A detection test must have one command with an explicit expectation.")
            prepared.append((world, commands[0]))
        return prepared

    def detects_fault(self, prepared, specification):
        for world, command in prepared:
            try:
                expression = self.parser.parseOneExpression_fromString(
                    world, "{\n" + specification + "\n}")
            except Exception as exc:
                raise TestExclusion("evaluation_error", str(exc)) from exc
            try:
                satisfiable = self.execute(world, command.change(
                    command.formula.and_(expression))).satisfiable()
            except Exception as exc:
                raise TestExclusion("solver_error", str(exc)) from exc
            if satisfiable != (command.expects == 1):
                return True
        return False


def fault_catalogue(key, requirement):
    if "erroneous" not in requirement:
        return None
    specifications = requirement["erroneous"]
    if not isinstance(specifications, list) or any(
            not isinstance(spec, str) or not spec.strip() for spec in specifications):
        raise ValueError(f"{key}: erroneous specifications must be a list of nonempty strings.")
    catalogue = {}
    for index, specification in enumerate(specifications, 1):
        specification = specification.strip()
        digest = hashlib.sha256(json.dumps(
            [*key, specification], ensure_ascii=False).encode()).hexdigest()
        entry = catalogue.setdefault(digest, {"id": digest, "specification": specification,
                                             "source_indices": []})
        entry["source_indices"].append(index)
    return catalogue


def load_runs(paths, valid_only=False):
    """Require the same tasks/models so missing tasks cannot masquerade as diversity."""
    if len(paths) < 2:
        raise ValueError("Pass at least two run JSON files.")
    resolved = [Path(path).resolve() for path in paths]
    if len(set(resolved)) != len(resolved):
        raise ValueError("Pass distinct run files, rather than the same file more than once.")
    runs, reference = [], None
    for index, path in enumerate(resolved, 1):
        with path.open() as handle:
            data = json.load(handle)
        if not isinstance(data, list) or not data:
            raise ValueError(f"{path}: expected a nonempty generation-results list.")
        tasks = {}
        examples = set()
        for example in data:
            name, model = example["example"], example["model"]
            if name in examples:
                raise ValueError(f"{path}: duplicate benchmark {name!r}.")
            examples.add(name)
            previous = []
            for requirement in example["requirements"]:
                pred = requirement["pred"].removeprefix("this/")
                key = (name, pred)
                if key in tasks:
                    raise ValueError(f"{path}: duplicate requirement {name} {pred}.")
                if not isinstance(requirement["instances"], str):
                    raise ValueError(f"{path}: {name} {pred} has no Alloy command text.")
                oracle = requirement.get("oracle")
                if not isinstance(oracle, str) or not oracle.strip():
                    raise ValueError(f"{path}: {name} {pred} needs an oracle for failure-recurrence analysis.")
                n, fallback = requested_n(requirement, path)
                tasks[key] = {"model": model.strip(), "requirement": requirement,
                              "previous": previous.copy(), "oracle": oracle,
                              "n": n, "count_from_filename": fallback,
                              "faults": fault_catalogue(key, requirement)}
                previous.append(oracle)
        if not tasks:
            raise ValueError(f"{path}: no requirements found.")
        if reference is not None:
            if tasks.keys() != reference.keys():
                raise ValueError(f"{path}: runs must contain the same benchmarks and requirements.")
            for key, task in tasks.items():
                first = reference[key]
                if task["model"] != first["model"]:
                    raise ValueError(f"{path}: model declarations differ for {key[0]} {key[1]}.")
                if (task["oracle"], task["previous"]) != (first["oracle"], first["previous"]):
                    raise ValueError(f"{path}: oracles or cumulative requirement order differ for {key}.")
                if ((task["faults"] is None) != (first["faults"] is None)
                        or task["faults"] is not None and task["faults"].keys() != first["faults"].keys()):
                    raise ValueError(f"{path}: erroneous specification sets differ for {key}.")
        else:
            reference = tasks
        runs.append({"id": f"run{index}", "path": str(path), "label": path.stem, "tasks": tasks})
    return runs


def set_statistics(sets):
    union = set().union(*sets.values())
    intersection = set.intersection(*sets.values()) if sets else set()
    frequency = Counter(sum(item in values for values in sets.values()) for item in union)
    pairs = []
    ids = list(sets)
    for i, left in enumerate(ids):
        for right in ids[i + 1:]:
            common, combined = sets[left] & sets[right], sets[left] | sets[right]
            pairs.append({"left": left, "right": right, "intersection": len(common),
                          "union": len(combined), "jaccard": len(common) / len(combined) if combined else None,
                          "left_only": len(sets[left] - sets[right]),
                          "right_only": len(sets[right] - sets[left]),
                          "identical": sets[left] == sets[right]})
    return {"union": len(union), "intersection": len(intersection),
            "jaccard": len(intersection) / len(union) if union else None,
            "identical": all(values == next(iter(sets.values())) for values in sets.values()),
            "frequency": {str(count): frequency[count] for count in range(1, len(sets) + 1)},
            "pairwise": pairs}


def failure_recurrence(runs, records):
    """Count invalid occurrences and recurrence of their requirements, for all cohorts."""
    run_ids = [run["id"] for run in runs]
    by_task = defaultdict(list)
    for record in records:
        by_task[(record["example"], record["requirement"], record["run"])].append(record)
    requirements = []
    affected = {run_id: set() for run_id in run_ids}
    totals = {run_id: Counter() for run_id in run_ids}
    stage_totals = {run_id: Counter() for run_id in run_ids}
    issue_totals = {run_id: Counter() for run_id in run_ids}
    for key, task in runs[0]["tasks"].items():
        rows = []
        for run_id in run_ids:
            tests = by_task[(*key, run_id)]
            counts = Counter(test["validity"] for test in tests)
            stages = Counter(test["failure_stage"] for test in tests if test["validity"] == "invalid")
            issues = Counter(test["failure_stage"] for test in tests if test["validity"] == "unassessed")
            row = {"run": run_id, "generated": len(tests), "valid": counts["valid"],
                   "invalid": counts["invalid"], "unassessed": counts["unassessed"],
                   "by_stage": {stage: stages[stage] for stage in FAILURE_STAGES},
                   "assessment_issues": dict(issues)}
            rows.append(row)
            totals[run_id].update({name: row[name] for name in ("generated", "valid", "invalid", "unassessed")})
            stage_totals[run_id].update(stages)
            issue_totals[run_id].update(issues)
            if row["invalid"]:
                affected[run_id].add(key)
        requirements.append({"example": key[0], "requirement": key[1],
                             "description": task["requirement"].get("description", ""),
                             "runs_with_invalid": sum(row["invalid"] > 0 for row in rows),
                             "runs_with_unassessed": sum(row["unassessed"] > 0 for row in rows),
                             "fully_assessed": not any(row["unassessed"] for row in rows),
                             "stage_recurrence": {stage: sum(row["by_stage"][stage] > 0 for row in rows)
                                                  for stage in FAILURE_STAGES},
                             "runs": rows})
    frequency = Counter(req["runs_with_invalid"] for req in requirements)
    assessed_frequency = Counter(req["runs_with_invalid"] for req in requirements if req["fully_assessed"])
    return {"method": FAILURE_METHOD, "requirement_count": len(requirements), "run_count": len(runs),
            "frequency": {str(k): frequency[k] for k in range(len(runs) + 1)},
            "fully_assessed_frequency": {str(k): assessed_frequency[k] for k in range(len(runs) + 1)},
            "stage_frequency": {stage: {str(k): sum(req["stage_recurrence"][stage] == k for req in requirements)
                                        for k in range(len(runs) + 1)} for stage in FAILURE_STAGES},
            "requirements_with_unassessed": sum(not req["fully_assessed"] for req in requirements),
            "requirement_overlap": set_statistics(affected),
            "runs": [{"run": run_id, **totals[run_id], "requirements_with_invalid": len(affected[run_id]),
                      "by_stage": {stage: stage_totals[run_id][stage] for stage in FAILURE_STAGES},
                      "assessment_issues": dict(issue_totals[run_id])} for run_id in run_ids],
            "requirements": requirements}


def detection_statistics(detected, universe):
    """Sets share one assessed fault universe; unknown outcomes are not misses."""
    missed = {run: universe - values for run, values in detected.items()}
    combined = set().union(*detected.values())
    best = max((len(values) for values in detected.values()), default=0)
    total = len(universe)
    return {"wrong": total, "detected": set_statistics(detected), "missed": set_statistics(missed),
            "best_single": best, "combined": len(combined), "gain": len(combined) - best,
            "best_single_coverage": best / total if total else None,
            "combined_coverage": len(combined) / total if total else None,
            "coverage_gain": (len(combined) - best) / total if total else None,
            "runs": [{"run": run, "detected": len(values), "missed": len(missed[run]),
                      "coverage": len(values) / total if total else None,
                      "exclusive": len(values - set().union(
                          *(other for name, other in detected.items() if name != run)))}
                     for run, values in detected.items()]}


def mean_defined(values):
    values = [value for value in values if value is not None]
    return sum(values) / len(values) if values else None


def detection_macro(requirements, run_ids):
    compared = [req["summary"] for req in requirements
                if req["summary"] is not None and req["summary"]["wrong"]]
    rows = [{"run": run, "coverage": mean_defined(
        next(row["coverage"] for row in req["runs"] if row["run"] == run) for req in compared)}
            for run in run_ids]
    combined = mean_defined(req["combined_coverage"] for req in compared)
    best = max((row["coverage"] for row in rows if row["coverage"] is not None), default=None)
    result = {"requirements": len(compared), "runs": rows,
              "combined_coverage": combined, "best_single_coverage": best,
              "coverage_gain": combined - best if combined is not None else None}
    for kind in ("detected", "missed"):
        values = [req[kind]["jaccard"] for req in compared]
        pairs = []
        for left_index, left in enumerate(run_ids):
            for right in run_ids[left_index + 1:]:
                observations = [next(pair["jaccard"] for pair in req[kind]["pairwise"]
                                     if (pair["left"], pair["right"]) == (left, right))
                                for req in compared]
                pairs.append({"left": left, "right": right,
                              "jaccard": mean_defined(observations),
                              "requirements": sum(value is not None for value in observations)})
        result[kind] = {"jaccard": mean_defined(values),
                        "requirements": sum(value is not None for value in values), "pairwise": pairs}
    return result


def fault_detection(runs, records, comparator, progress=None):
    run_ids = [run["id"] for run in runs]
    by_task = defaultdict(list)
    for record in records:
        by_task[(record["example"], record["requirement"], record["run"])].append(record)
    requirements, pooled_universe = [], set()
    pooled = {run: set() for run in run_ids}
    for key, task in runs[0]["tasks"].items():
        suites, reasons = [], []
        sources = {}
        for run in runs:
            run_id = run["id"]
            own_task = run["tasks"][key]
            tests = by_task[(*key, run_id)]
            counts = Counter(test["validity"] for test in tests)
            polarities = Counter(test.get("polarity") for test in tests)
            n = own_task["n"]
            complete = complete_suite(n, len(tests), polarities["positive"],
                                      polarities["negative"], counts["valid"])
            suites.append({"run": run_id, "requested_per_polarity": n,
                           "count_from_filename": own_task["count_from_filename"],
                           "generated": len(tests), "valid": counts["valid"],
                           "invalid": counts["invalid"], "unassessed": counts["unassessed"],
                           "positive": polarities["positive"], "negative": polarities["negative"],
                           "complete": complete})
            if not complete:
                reasons.append(f"{run_id}: " + ("unknown requested count" if n is None else
                                                "suite is not complete and valid"))
            sources[run_id] = tuple(test["command"] for test in tests if test["validity"] == "valid")
        if task["faults"] is None:
            reasons.append("No erroneous-specification catalogue was supplied.")
        row = {"example": key[0], "requirement": key[1],
               "description": task["requirement"].get("description", ""),
               "included": not reasons, "reasons": reasons, "suites": suites,
               "faults": [], "summary": None}
        requirements.append(row)
        if reasons:
            continue
        if progress:
            progress(f"Comparing fault detection {key[0]} / {key[1]}")
        prepared, preparation_errors = {}, []
        try:
            for suite in dict.fromkeys(sources.values()):
                prepared[suite] = comparator.prepare_detection_suite(task, suite)
        except Exception as exc:
            preparation_errors.append(str(exc))
        detected = {run: set() for run in run_ids}
        universe = set()
        for index, entry in enumerate(task["faults"].values(), 1):
            fault = {**entry, "outcomes": []}
            row["faults"].append(fault)
            if progress and index % 50 == 0:
                progress(f"  {key[0]} / {key[1]}: {index}/{len(task['faults'])} specifications")
            if preparation_errors:
                fault.update(status="unassessed", stage="suite_error", reason="; ".join(preparation_errors))
                continue
            try:
                comparator.validate_fault(task, entry["specification"])
            except TestExclusion as exc:
                fault.update(status="excluded", stage=exc.stage, reason=str(exc))
                continue
            outcomes = {}
            for run in run_ids:
                suite = sources[run]
                if suite not in outcomes:
                    try:
                        found = comparator.detects_fault(prepared[suite], entry["specification"])
                    except TestExclusion as exc:
                        outcomes[suite] = {"status": "unassessed", "stage": exc.stage, "reason": str(exc)}
                    else:
                        outcomes[suite] = {"status": "detected" if found else "missed"}
                fault["outcomes"].append({"run": run, **outcomes[suite]})
            if any(outcome["status"] == "unassessed" for outcome in fault["outcomes"]):
                fault["status"] = "unassessed"
                continue
            fault["status"] = "assessed"
            universe.add(entry["id"])
            for outcome in fault["outcomes"]:
                if outcome["status"] == "detected":
                    detected[outcome["run"]].add(entry["id"])
        row["summary"] = detection_statistics(detected, universe)
        for run_row in row["summary"]["runs"]:
            run_id = run_row["run"]
            run_row["detected_ids"] = sorted(detected[run_id])
            run_row["missed_ids"] = sorted(universe - detected[run_id])
            pooled[run_id].update(detected[run_id])
        pooled_universe.update(universe)
        row["excluded_faults"] = sum(fault["status"] == "excluded" for fault in row["faults"])
        row["unassessed_faults"] = sum(fault["status"] == "unassessed" for fault in row["faults"])
    summary = detection_statistics(pooled, pooled_universe)
    summary["macro"] = detection_macro(requirements, run_ids)
    return {"method": DETECTION_METHOD, "requirement_count": len(requirements),
            "included_requirements": sum(req["included"] for req in requirements),
            "excluded_faults": sum(req.get("excluded_faults", 0) for req in requirements),
            "unassessed_faults": sum(req.get("unassessed_faults", 0) for req in requirements),
            "summary": summary, "requirements": requirements}


def compare_runs(runs, comparator, valid_only=False, progress=None):
    """Build one class catalogue across every run, not a separate catalogue per pair."""
    run_ids = [run["id"] for run in runs]
    classes, records, buckets = [], [], {}
    stage_counts = {run_id: Counter() for run_id in run_ids}
    excluded = {run_id: Counter() for run_id in run_ids}
    # Cache duplicate commands without retaining their Java worlds/solutions.
    cache = {}
    for key in runs[0]["tasks"]:
        if progress:
            progress(f"Comparing {key[0]} / {key[1]}")
        for run in runs:
            run_id = run["id"]
            task = run["tasks"][key]
            commands = generated_test_sources(task["requirement"])
            for index, source in enumerate(commands, 1):
                record = {"run": run_id, "example": key[0], "requirement": key[1],
                          "test": index, "command": source}
                stage_counts[run_id]["generated"] += 1
                cache_key = (key, source)
                if cache_key in cache:
                    cached, stages = cache[cache_key]
                    record.update(cached)
                    stage_counts[run_id].update(stages)
                else:
                    stages = []
                    try:
                        solved = comparator.solve(task["model"], source, stages.append)
                        record["polarity"] = solved.polarity
                        try:
                            comparator.require_valid(solved, task["previous"], task["oracle"])
                        except TestExclusion as exc:
                            record.update(validity="invalid", failure_stage=exc.stage, reason=str(exc))
                            if valid_only:
                                raise
                        else:
                            record["validity"] = "valid"
                        bucket_key = (*key, solved.polarity)
                        profiles = buckets.setdefault(bucket_key, defaultdict(list))
                        compatible = profiles[solved.profile]
                        matched = next((entry for entry in compatible
                                        if comparator.matches(solved, entry["predicate"])), None)
                        if matched is None:
                            matched = {"id": f"C{len(classes) + 1:05d}", "example": key[0],
                                       "requirement": key[1], "polarity": solved.polarity,
                                       "predicate": solved.predicate, "occurrences": []}
                            classes.append(matched)
                            compatible.append(matched)
                        record.update(status="compared", **{"class": matched["id"]})
                    except TestExclusion as exc:
                        record.update(status="excluded", exclusion=exc.stage, reason=str(exc),
                                      validity="unassessed" if exc.stage in ASSESSMENT_ISSUES else "invalid",
                                      failure_stage=exc.stage)
                    cache[cache_key] = ({k: v for k, v in record.items()
                                         if k not in ("run", "example", "requirement", "test", "command")}, stages)
                    stage_counts[run_id].update(stages)
                if record["status"] == "excluded":
                    excluded[run_id][record["exclusion"]] += 1
                else:
                    classes[int(record["class"][1:]) - 1]["occurrences"].append(
                        {"run": run_id, "test": index})
                    stage_counts[run_id]["compared"] += 1
                records.append(record)
    sets = {run_id: set() for run_id in run_ids}
    for entry in classes:
        entry["runs"] = [run_id for run_id in run_ids
                         if any(item["run"] == run_id for item in entry["occurrences"])]
        for run_id in entry["runs"]:
            sets[run_id].add(entry["id"])
    summary = set_statistics(sets)
    summary["runs"] = []
    for run_id in run_ids:
        counts = {stage: stage_counts[run_id][stage] for stage in
                  ("generated", "parsed", "consistent", "unique", "compared")}
        counts.update(run=run_id, distinct=len(sets[run_id]),
                      duplicates=counts["compared"] - len(sets[run_id]),
                      exclusive=sum(entry["runs"] == [run_id] for entry in classes),
                      exclusions=dict(excluded[run_id]))
        summary["runs"].append(counts)
    groups = []
    for key in runs[0]["tasks"]:
        for polarity in ("positive", "negative"):
            members = [entry for entry in classes if (entry["example"], entry["requirement"],
                                                      entry["polarity"]) == (*key, polarity)]
            group_sets = {run_id: {entry["id"] for entry in members if run_id in entry["runs"]}
                          for run_id in run_ids}
            group = {"example": key[0], "requirement": key[1], "polarity": polarity,
                     **set_statistics(group_sets), "runs": []}
            for run_id in run_ids:
                count = sum(item["run"] == run_id for entry in members for item in entry["occurrences"])
                group["runs"].append({"run": run_id, "compared": count,
                                      "distinct": len(group_sets[run_id]),
                                      "duplicates": count - len(group_sets[run_id]),
                                      "exclusive": sum(entry["runs"] == [run_id] for entry in members)})
            groups.append(group)
    return {"version": 3, "method": METHOD,
            "cohort": "valid" if valid_only else "consistent and unique",
            "runs": [{k: run[k] for k in ("id", "path", "label")} for run in runs],
            "summary": summary, "groups": groups, "classes": classes, "tests": records,
            "failure_recurrence": failure_recurrence(runs, records),
            "fault_detection": fault_detection(runs, records, comparator, progress)}


def failure_markdown(failures):
    def cell(value):
        return str(value).replace("|", "\\|").replace("\n", " ")

    def percent(value):
        return f"{100 * value:.2f}%" if value is not None else "—"

    run_ids = [row["run"] for row in failures["runs"]]
    lines = ["## Invalid-test recurrence", "", failures["method"], "",
             "This section covers all generated commands, including those excluded by `--valid-only`.", "",
             "| Run | Generated | Valid | Invalid | Unassessed | Requirements with invalid tests |",
             "| --- | ---: | ---: | ---: | ---: | ---: |"]
    for row in failures["runs"]:
        lines.append("| " + " | ".join(str(row[key]) for key in
                     ("run", "generated", "valid", "invalid", "unassessed", "requirements_with_invalid")) + " |")
    overlap = failures["requirement_overlap"]
    lines += ["", f"Requirements with invalid tests in at least one run: **{overlap['union']}**. "
              f"Requirements with invalid tests in every run: **{overlap['intersection']}**. "
              f"All-run Jaccard of affected-requirement sets: **{percent(overlap['jaccard'])}**.", "",
              "| Observed invalid tests in this many runs | Requirements | Of these, fully assessed |",
              "| ---: | ---: | ---: |"]
    for k, count in failures["frequency"].items():
        lines.append(f"| {k}/{len(run_ids)} | {count} | {failures['fully_assessed_frequency'][k]} |")
    if failures["requirements_with_unassessed"]:
        lines += ["", f"**{failures['requirements_with_unassessed']} requirement(s)** have unassessed commands. "
                  "Observed recurrence can undercount failures there; zero observed failures does not establish validity."]
    lines += ["", "### Invalid-test counts per requirement", "",
              "| Benchmark | Requirement | Runs with invalid tests | " + " | ".join(run_ids) + " | Unassessed commands |",
              "| --- | --- | ---: | " + " | ".join("---:" for _ in run_ids) + " | ---: |"]
    for req in failures["requirements"]:
        values = [req["example"], req["requirement"], f"{req['runs_with_invalid']}/{len(run_ids)}",
                  *[row["invalid"] for row in req["runs"]], sum(row["unassessed"] for row in req["runs"])]
        lines.append("| " + " | ".join(map(cell, values)) + " |")
    lines += ["", "### Recurrence by first failing stage", "",
              "Only stages with observed failures are listed. Counts are invalid command occurrences, "
              "including repetitions within a run.", "",
              "| Benchmark | Requirement | First failing stage | Runs with this failure | " + " | ".join(run_ids) + " |",
              "| --- | --- | --- | ---: | " + " | ".join("---:" for _ in run_ids) + " |"]
    observed = False
    for req in failures["requirements"]:
        for stage in FAILURE_STAGES:
            count = req["stage_recurrence"][stage]
            if not count:
                continue
            observed = True
            values = [req["example"], req["requirement"], stage, f"{count}/{len(run_ids)}",
                      *[row["by_stage"][stage] for row in req["runs"]]]
            lines.append("| " + " | ".join(map(cell, values)) + " |")
    if not observed:
        lines += ["", "No confirmed invalid commands were found."]
    lines += ["", "### Pairwise overlap of affected requirements", "",
              "| Runs | Affected in both | Affected in either | Jaccard | Same affected requirements |",
              "| --- | ---: | ---: | ---: | :---: |"]
    for row in overlap["pairwise"]:
        lines.append(f"| {row['left']} / {row['right']} | {row['intersection']} | {row['union']} | "
                     f"{percent(row['jaccard'])} | {'yes' if row['identical'] else 'no'} |")
    return lines


def detection_markdown(detection):
    def cell(value):
        return str(value).replace("|", "\\|").replace("\n", " ")

    def percent(value):
        return f"{100 * value:.2f}%" if value is not None else "—"

    def points(value):
        return f"{100 * value:.2f}" if value is not None else "—"

    summary = detection["summary"]
    macro = summary["macro"]
    lines = ["## Overlap in detected and missed specifications", "", detection["method"], "",
             f"Requirements with complete valid suites and a shared catalogue: "
             f"**{detection['included_requirements']}/{detection['requirement_count']}**. "
             f"Requirements with at least one assessed specification: **{macro['requirements']}**. "
             f"Assessed specifications: **{summary['wrong']}**. "
             f"Unparseable specifications excluded: **{detection['excluded_faults']}**. "
             f"Specifications with assessment gaps: **{detection['unassessed_faults']}**.", "",
             "### Detection and benefit of combining runs", "",
             "Coverage below is the unweighted mean of per-requirement detection rates on the shared "
             "assessed catalogue. Counts are pooled; they do not determine the mean coverage. "
             "`Only this run` counts specifications detected by that run and missed by every other run.", "",
             "| Run | Detected | Missed | Only this run | Mean coverage |",
             "| --- | ---: | ---: | ---: | ---: |"]
    means = {row["run"]: row["coverage"] for row in macro["runs"]}
    for row in summary["runs"]:
        lines.append(f"| {row['run']} | {row['detected']} | {row['missed']} | {row['exclusive']} | "
                     f"{percent(means[row['run']])} |")
    lines += ["", f"Combined mean coverage: **{percent(macro['combined_coverage'])}**; "
              f"best individual run: **{percent(macro['best_single_coverage'])}**; "
              f"gain: **{points(macro['coverage_gain'])} percentage points**.", "",
              f"Pooled combined detection: **{summary['combined']}/{summary['wrong']}**; "
              f"best individual run: **{summary['best_single']}**; "
              f"additional specifications detected: **{summary['gain']}**.", "",
              "The combined result uses every test from every run and therefore a larger test budget. "
              "Mean coverage gain compares the combined suite with the best single run across the "
              "shared requirements, rather than selecting a different best run for each requirement.", "",
              "### Pairwise overlap of detected and missed sets", "",
              "Primary Jaccard values are averaged per requirement. The number of contributing "
              "requirements can differ between detected and missed sets because empty unions are undefined.", "",
              "| Runs | Mean detected Jaccard | Requirements | Mean missed Jaccard | Requirements |",
              "| --- | ---: | ---: | ---: | ---: |"]
    for detected, missed in zip(macro["detected"]["pairwise"], macro["missed"]["pairwise"]):
        lines.append(f"| {detected['left']} / {detected['right']} | {percent(detected['jaccard'])} | "
                     f"{detected['requirements']} | {percent(missed['jaccard'])} | {missed['requirements']} |")
    lines += ["", "Pooled overlap is also shown; requirements with more faulty specifications have more weight here.", "",
              "| Runs | Detected shared | Detected union | Detected Jaccard | Left only | Right only | Missed shared | Missed union | Missed Jaccard |",
              "| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |"]
    for detected, missed in zip(summary["detected"]["pairwise"], summary["missed"]["pairwise"]):
        values = [f"{detected['left']} / {detected['right']}", detected["intersection"], detected["union"],
                  percent(detected["jaccard"]), detected["left_only"], detected["right_only"],
                  missed["intersection"], missed["union"], percent(missed["jaccard"])]
        lines.append("| " + " | ".join(map(str, values)) + " |")
    for kind in ("detected", "missed"):
        stats = summary[kind]
        lines += ["", f"**{kind.capitalize()} in all runs:** {stats['intersection']}; "
                  f"**{kind} in any run:** {stats['union']}; "
                  f"mean all-run Jaccard: **{percent(macro[kind]['jaccard'])}** "
                  f"({macro[kind]['requirements']} requirements); "
                  f"pooled all-run Jaccard: **{percent(stats['jaccard'])}**."]
    lines += ["", "### Fault detection per requirement", "",
              "Per-requirement gain uses that requirement's best individual suite as its baseline.", "",
              "| Benchmark | Requirement | Assessed faults | Best run | Combined | Gain | Gain (pp) | Detected Jaccard | Missed Jaccard |",
              "| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |"]
    for req in detection["requirements"]:
        stats = req["summary"]
        if stats is None:
            continue
        values = [req["example"], req["requirement"], stats["wrong"], stats["best_single"],
                  stats["combined"], stats["gain"], points(stats["coverage_gain"]),
                  percent(stats["detected"]["jaccard"]), percent(stats["missed"]["jaccard"])]
        lines.append("| " + " | ".join(map(cell, values)) + " |")
    omitted = [req for req in detection["requirements"] if not req["included"]]
    if omitted:
        lines += ["", "### Requirements excluded from fault-detection comparison", "",
                  "Structural comparison and invalid-test recurrence still include these requirements.", "",
                  "| Benchmark | Requirement | Reason |", "| --- | --- | --- |"]
        for req in omitted:
            lines.append("| " + " | ".join(map(cell, [req["example"], req["requirement"],
                                                       "; ".join(req["reasons"])])) + " |")
    gaps = [req for req in detection["requirements"] if req.get("excluded_faults") or req.get("unassessed_faults")]
    if gaps:
        lines += ["", "### Catalogue and assessment gaps", "",
                  "These specifications are excluded from every run's coverage and miss sets. "
                  "Comparisons concern only the remaining assessed catalogue. Reasons and per-run "
                  "outcomes are retained in JSON.", "",
                  "| Benchmark | Requirement | Unparseable | Unassessed |", "| --- | --- | ---: | ---: |"]
        for req in gaps:
            lines.append("| " + " | ".join(map(cell, [req["example"], req["requirement"],
                                                       req["excluded_faults"], req["unassessed_faults"]])) + " |")
    lines += ["", "The JSON report includes stable specification IDs and source text, per-run detected/missed "
              "IDs, individual outcomes, per-requirement overlap and gains, and catalogue exclusions."]
    return lines


def markdown(report):
    def cell(value):
        return str(value).replace("|", "\\|").replace("\n", " ")

    def percent(value):
        return f"{100 * value:.2f}%" if value is not None else "—"

    lines = ["# Structural and fault-detection overlap between generated test runs", "", METHOD, "",
             f"Cohort: **{report['cohort']}**. " + (
                 "Structural overlap includes only tests passing all validity checks."
                 if report["cohort"] == "valid" else
                 "Structural overlap includes consistent, unique tests even when they fail earlier requirements or have incorrect labels."),
             "Validity is always checked afresh for the separate invalid-test recurrence section.", ""]
    lines += [f"- **{run['id']}**: `{run['path']}`" for run in report["runs"]]
    lines += ["", "## Per-run diversity", "",
              "`Distinct` counts different structures within that run. `Duplicates` counts repeated occurrences "
              "beyond the first. `Only this run` counts distinct classes absent from every other supplied run. "
              "These counts keep requirements and intended polarities separate.", "",
              "| Run | Generated | Compared | Distinct | Duplicates | Only this run | Excluded |",
              "| --- | ---: | ---: | ---: | ---: | ---: | ---: |"]
    for row in report["summary"]["runs"]:
        lines.append("| " + " | ".join(map(str, (row["run"], row["generated"], row["compared"],
                     row["distinct"], row["duplicates"], row["exclusive"], sum(row["exclusions"].values())))) + " |")
    exclusions = sorted({stage for row in report["summary"]["runs"] for stage in row["exclusions"]})
    if exclusions:
        lines += ["", "Exclusions (first failing stage; commands and reasons are retained in the JSON report):", "",
                  "| Run | " + " | ".join(exclusions) + " |", "| --- | " + " | ".join("---:" for _ in exclusions) + " |"]
        for row in report["summary"]["runs"]:
            lines.append("| " + row["run"] + " | " + " | ".join(str(row["exclusions"].get(stage, 0)) for stage in exclusions) + " |")
    summary = report["summary"]
    lines += ["", "## Overlap across all runs", "",
              f"Union: **{summary['union']}** distinct classes. Present in every run: **{summary['intersection']}**. "
              f"All-run Jaccard (intersection / union): **{percent(summary['jaccard'])}**. "
              f"All structural sets identical: **{'yes' if summary['identical'] else 'no'}**.", "",
              "| Number of runs containing a class | Classes |", "| ---: | ---: |"]
    lines += [f"| {count} | {total} |" for count, total in summary["frequency"].items()]
    lines += ["", "## Pairwise overlap", "",
              "Jaccard = shared classes / union of classes. Empty unions have no defined percentage. "
              "Counts use sets, so repeated tests do not increase overlap.", "",
              "| Runs | Shared | Union | Jaccard | Left only | Right only | Same set |",
              "| --- | ---: | ---: | ---: | ---: | ---: | :---: |"]
    for row in summary["pairwise"]:
        lines.append(f"| {row['left']} / {row['right']} | {row['intersection']} | {row['union']} | "
                     f"{percent(row['jaccard'])} | {row['left_only']} | {row['right_only']} | "
                     f"{'yes' if row['identical'] else 'no'} |")
    lines += [""] + failure_markdown(report["failure_recurrence"])
    lines += [""] + detection_markdown(report["fault_detection"])
    lines += ["", "## Distinct structures per requirement and polarity", "",
              "| Benchmark | Requirement | Polarity | Union | In every run | " + " | ".join(run["id"] for run in report["runs"]) + " |",
              "| --- | --- | --- | ---: | ---: | " + " | ".join("---:" for _ in report["runs"]) + " |"]
    for group in report["groups"]:
        lines.append("| " + " | ".join(map(cell, [group["example"], group["requirement"], group["polarity"],
                     group["union"], group["intersection"], *[row["distinct"] for row in group["runs"]]])) + " |")
    lines += ["", "Class IDs, complete representative predicates, every command's class assignment, "
              "per-requirement pairwise statistics, and exclusions are available in the JSON report.", ""]
    return "\n".join(lines)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("jar", help="AlloyTools jar (use Alloy 6, not the AlloyMax jar)")
    parser.add_argument("runs", nargs="+", help="two or more generation-results JSON files")
    parser.add_argument("-o", "--output", default="test_overlap", metavar="PREFIX",
                        help="output prefix for .md and .json reports (default: test_overlap)")
    parser.add_argument("--valid-only", action="store_true",
                        help="restrict structural overlap to valid tests; failure recurrence covers all commands, "
                             "and fault detection always uses requirements complete and valid in every run")
    args = parser.parse_args(argv)
    try:
        runs = load_runs(args.runs, args.valid_only)
        if not Path(args.jar).is_file():
            raise ValueError(f"Alloy jar not found: {args.jar}")
        destinations = [Path(args.output + suffix).resolve() for suffix in (".json", ".md")]
        if set(destinations) & {Path(run["path"]) for run in runs}:
            raise ValueError("Output reports must not overwrite input runs.")
        report = compare_runs(runs, AlloyComparator(args.jar), args.valid_only,
                              progress=lambda message: print(message, file=sys.stderr, flush=True))
        for destination in destinations:
            destination.parent.mkdir(parents=True, exist_ok=True)
        destinations[0].write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
        destinations[1].write_text(markdown(report))
    except (ValueError, KeyError, OSError) as exc:
        parser.exit(1, f"Error: {exc}\n")
    for row in report["summary"]["runs"]:
        print(f"{row['run']}: {row['compared']} compared, {row['distinct']} distinct, "
              f"{row['duplicates']} duplicates, {row['exclusive']} only in this run; "
              f"{sum(row['exclusions'].values())} excluded")
    detection = report["fault_detection"]
    print(f"Fault detection: {detection['included_requirements']} shared complete requirements, "
          f"{detection['summary']['wrong']} assessed specifications; "
          f"{detection['summary']['gain']} additional specifications detected by combining runs")
    print("Reports: " + ", ".join(map(str, destinations)))


if __name__ == "__main__":
    main()
