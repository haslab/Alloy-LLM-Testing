"""Measure top-level signature sizes in generated Alloy tests.

With no input paths, analyze the five GPT-5 few-shot runs used in RQ5.
Historical validity classifications are read, never rewritten or recomputed.
Alloy solves only the scenario and its model declarations, without the oracle.
"""

import argparse
from collections import Counter
import csv
from datetime import datetime
import hashlib
import json
from pathlib import Path
import re
import statistics
import sys
from zoneinfo import ZoneInfo


ROOT = Path(__file__).resolve().parents[1]
RQ5_RUNS = (
    "gpt-5-2025-08-07_210925_few1",
    "gpt-5-2025-08-07_220925_few2",
    "gpt-5-2025-08-07_200925_few3",
    "gpt-5-2025-08-07_230925_few4",
    "gpt-5-2025-08-07_230925_few5",
)
# Match exactly the commands that the original analysis extracted.
TEST_PATTERN = re.compile(r"run(?: \w*)? \{(?:.|\n)*?expect [0-1]", re.MULTILINE)
FAILURE_STAGES = ("parse", "consistent", "previous", "valid")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def top_level_sigs(world):
    """Count abstract parents, but not their children, subset sigs, or built-ins."""
    return {
        str(sig.label).removeprefix("this/"): sig
        for sig in world.getAllReachableSigs()
        if str(sig.label).startswith("this/")
        and hasattr(sig, "parent") and str(sig.parent.label) == "univ"
    }


def textual_bounds(test, roots):
    """Also retain the explicit bounds of syntactically invalid commands."""
    tail = test[test.rfind("}") + 1:]
    bounds = {name: int(n) for n, name in re.findall(r"(?:exactly\s+)?(\d+)\s+(\w+)", tail)}
    return {name: bounds[name] for name in roots} if all(name in bounds for name in roots) else None


class ScopeAnalyzer:
    def __init__(self):
        from edu.mit.csail.sdg.parser import CompUtil
        from edu.mit.csail.sdg.translator import A4Options, TranslateAlloyToKodkod
        from kodkod.engine.satlab import SATFactory

        self.parse = CompUtil.parseEverything_fromString
        self.expression = CompUtil.parseOneExpression_fromString
        self.execute = TranslateAlloyToKodkod.execute_command
        self.options = A4Options()
        self.options.solver = SATFactory.get("sat4j")

    def solve(self, world, command):
        return self.execute(None, world.getAllReachableSigs(), command, self.options)

    def bounds(self, command, roots):
        explicit = {str(s.sig.label): int(s.endingScope) for s in command.scope}
        default = int(command.overall) if int(command.overall) >= 0 else 3
        result = {}
        for name, sig in roots.items():
            if str(sig.label) not in explicit:
                # Abstract-parent bounds can be inferred from child scopes by
                # Alloy. Do not silently replace those with an overall bound.
                if any(hasattr(s.sig, "parent") and s.sig.parent == sig for s in command.scope):
                    raise ValueError(f"Specify an explicit top-level scope for {name}; child scopes alone are unsupported")
            result[name] = explicit.get(str(sig.label), default)
        return result

    def measure(self, model, test):
        try:
            world = self.parse(None, model + "\n" + test)
        except Exception as exc:
            return {"measurement": "parse_error", "measurement_error": str(exc).splitlines()[0]}
        roots = top_level_sigs(world)
        command = world.getAllCommands()[0]
        bounds = self.bounds(command, roots)
        result = {"declared_bounds": bounds, "declared_maximum": max(bounds.values(), default=0)}
        try:
            solution = self.solve(world, command)
        except Exception as exc:
            return dict(result, measurement="solver_error", measurement_error=str(exc).splitlines()[0])
        if not solution.satisfiable():
            return dict(result, measurement="unsatisfiable")
        witness = {name: int(solution.eval(sig).size()) for name, sig in roots.items()}
        maxima = dict(witness)
        for name, sig in roots.items():
            low, high = witness[name], bounds[name]
            while low < high:
                middle = (low + high + 1) // 2
                variables = ", ".join(f"scopeStatsAtom{i}" for i in range(middle))
                # Count with distinct quantified atoms, avoiding Int overflow.
                at_least = self.expression(world, f"some disj {variables} : {sig.label} | no none")
                stronger = command.change(command.formula.and_(at_least))
                if self.solve(world, stronger).satisfiable():
                    low = middle
                else:
                    high = middle - 1
            maxima[name] = low
        return dict(result, measurement="measured", witness_atoms=witness,
                    maximum_atoms_by_signature=maxima,
                    maximum_atoms=max(maxima.values(), default=0),
                    larger_than_first_witness=maxima != witness)


def assign_failures(tests, failures):
    """Keep occurrence counts: identical test texts need not be unique."""
    unknown = set(failures) - set(FAILURE_STAGES)
    if unknown:
        raise ValueError(f"Unknown historical failure stages: {sorted(unknown)}")
    remaining = {stage: Counter(failures.get(stage, [])) for stage in FAILURE_STAGES}
    assigned = []
    for test in tests:
        stage = next((s for s in FAILURE_STAGES if remaining[s][test]), None)
        if stage:
            remaining[stage][test] -= 1
        assigned.append(stage)
    if any(+counts for counts in remaining.values()):
        raise ValueError("Historical failures contain commands absent from the execution snapshot")
    return assigned


def summarize(rows, reference, value="maximum_atoms"):
    values = [row[value] for row in rows if row.get(value) is not None]
    above = sum(v > reference for v in values)
    return {
        "count": len(rows), "measured": len(values), "unavailable": len(rows) - len(values),
        "min": min(values, default=None), "mean": statistics.mean(values) if values else None,
        "median": statistics.median(values) if values else None, "max": max(values, default=None),
        "histogram": dict(sorted(Counter(values).items())), "above_reference": above,
        "at_most_reference": len(values) - above,
        "above_reference_percent": 100 * above / len(values) if values else None,
    }


def saved_totals(path):
    with path.open(newline="") as stream:
        rows = list(csv.DictReader(stream, delimiter="\t"))
    total = next(row for row in rows if row["Requirement"] == "Totals")
    return {key: int(total[key]) for key in ("Tests", "Syntax", "Consistent", "Previous", "Valid", "Complete")}


def analyze_run(path, failure_dir, analyzer, reference):
    match = re.search(r"_(?:few|one|zero)(\d+)$", path.stem)
    if not match:
        raise ValueError(f"Cannot infer requested n from {path.name}; expected a suffix such as _few3.json")
    n = int(match.group(1))
    failure_path = failure_dir / (path.stem + "_failures.json")
    summary_path = failure_dir / (path.stem + ".txt")
    dataset = json.loads(path.read_text())
    failures = json.loads(failure_path.read_text())
    tests, suites = [], []
    for example in dataset:
        roots = top_level_sigs(analyzer.parse(None, example["model"]))
        for req in example["requirements"]:
            commands = TEST_PATTERN.findall(req["instances"])
            stages = assign_failures(commands, failures.get(example["example"], {}).get(req["pred"], {}))
            complete = len(commands) == 2 * n and not any(stages)
            current = []
            for index, (command, stage) in enumerate(zip(commands, stages), 1):
                row = {
                    "run": path.stem, "n": n, "example": example["example"], "invariant": req["pred"],
                    "test_index": index, "label": re.match(r"run\s+(\w+)\s*\{", command).group(1)
                    if re.match(r"run\s+(\w+)\s*\{", command) else "",
                    "polarity": "positive" if command.endswith("expect 1") else "negative",
                    "historical_failure": stage, "historically_valid": stage is None,
                    "complete_valid_suite": complete,
                }
                fallback = textual_bounds(command, roots)
                if fallback is not None:
                    row.update(declared_bounds=fallback, declared_maximum=max(fallback.values(), default=0))
                row.update(analyzer.measure(example["model"], command))
                if row["historically_valid"] and row["measurement"] != "measured":
                    raise ValueError(f"A historically valid test could not be measured: {path.name}, {req['pred']}, {index}")
                row["above_reference"] = row.get("maximum_atoms", 0) > reference if row["measurement"] == "measured" else None
                tests.append(row)
                current.append(row)
            suite = {
                "run": path.stem, "n": n, "example": example["example"], "invariant": req["pred"],
                "description": req["description"], "tests": len(commands),
                "historically_valid_tests": sum(row["historically_valid"] for row in current),
                "complete_valid_suite": complete,
                "maximum_atoms": max((row["maximum_atoms"] for row in current), default=0)
                if all(row["measurement"] == "measured" for row in current) else None,
            }
            suites.append(suite)
    stages = Counter(row["historical_failure"] for row in tests)
    counts = [len(tests)]
    for stage in FAILURE_STAGES:
        counts.append(counts[-1] - stages[stage])
    observed = dict(zip(("Tests", "Syntax", "Consistent", "Previous", "Valid"), counts))
    observed["Complete"] = sum(row["complete_valid_suite"] for row in suites)
    historical = saved_totals(summary_path)
    if observed != historical:
        raise ValueError(f"Historical summary mismatch for {path.name}: observed {observed}, saved {historical}")
    populations = {
        "all_generated": tests,
        "historically_valid": [r for r in tests if r["historically_valid"]],
        "rq5_complete_tests": [r for r in tests if r["complete_valid_suite"]],
        "rq5_complete_suites": [r for r in suites if r["complete_valid_suite"]],
    }
    complete_tests = populations["rq5_complete_tests"]
    return {
        "run": path.stem, "n": n, "historical_totals": historical,
        "inputs": [{"path": str(p.resolve()), "sha256": digest(p)} for p in (path, failure_path, summary_path)],
        "populations": {name: summarize(rows, reference) for name, rows in populations.items()},
        "declared_scopes_all_generated": summarize(tests, reference, "declared_maximum"),
        "by_example_rq5": {example: summarize([r for r in complete_tests if r["example"] == example], reference)
                           for example in dict.fromkeys(r["example"] for r in tests)},
        "by_polarity_rq5": {kind: summarize([r for r in complete_tests if r["polarity"] == kind], reference)
                            for kind in ("positive", "negative")},
    }, tests, suites


def format_number(value):
    return "—" if value is None else f"{value:.2f}"


def report(document, tests, suites):
    ref = document["reference_scope"]
    lines = [
        "# Scope of GPT-5 tests used in RQ5", "",
        f"Generated: {document['generated_at']}. Reference bound: **{ref}** atoms per top-level signature.", "",
        "The primary population is the complete valid suites used by the saved RQ5 analysis. "
        "Validity labels and suite membership come from the historical failure files and are cross-checked "
        "against the saved summaries. This report does not repair or revalidate the old oracles.", "",
        "A test's size is the largest cardinality of any top-level signature, not their sum. "
        "Abstract parents such as Product are counted; children, subset signatures, Int, String, and "
        "the ordering module's implementation signature are excluded. Alloy evaluates atom counts in Java. "
        "For a partially specified test, additional SAT queries find the maximum attainable size under "
        "the model declarations; a first solver witness is not treated as an exact size. "
        "Unparseable or unsatisfiable tests have no measured size. Declared command bounds are also saved separately.", "",
        "## Tests in complete valid suites", "",
        f"| n | Complete suites | Tests | Mean size | Median | Maximum | Tests >{ref} | Suites entirely ≤{ref} | Suites with a test >{ref} |",
        "|---:|---:|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for run in document["runs"]:
        t = run["populations"]["rq5_complete_tests"]
        s = run["populations"]["rq5_complete_suites"]
        lines.append(f"| {run['n']} | {s['count']} | {t['count']} | {format_number(t['mean'])} | "
                     f"{format_number(t['median'])} | {t['max']} | {t['above_reference']} "
                     f"({format_number(t['above_reference_percent'])}%) | {s['at_most_reference']} | {s['above_reference']} |")
    maximum = max((r.get("maximum_atoms", 0) for r in tests), default=0)
    sizes = range(maximum + 1)
    lines += ["", "## Distribution of test sizes in complete valid suites", "",
              "| n | " + " | ".join(str(size) for size in sizes) + " |",
              "|---:|" + "---:|" * len(sizes)]
    for run in document["runs"]:
        hist = run["populations"]["rq5_complete_tests"]["histogram"]
        lines.append(f"| {run['n']} | " + " | ".join(str(hist.get(size, 0)) for size in sizes) + " |")
    lines += ["", "## All generated tests and all historically valid tests", "",
              f"| n | Generated | Measured | Unavailable | Mean size | Maximum | Measured >{ref} | Historically valid | Valid >{ref} |",
              "|---:|---:|---:|---:|---:|---:|---:|---:|---:|"]
    for run in document["runs"]:
        a = run["populations"]["all_generated"]
        v = run["populations"]["historically_valid"]
        lines.append(f"| {run['n']} | {a['count']} | {a['measured']} | {a['unavailable']} | "
                     f"{format_number(a['mean'])} | {a['max']} | {a['above_reference']} | {v['count']} | {v['above_reference']} |")
    lines += ["", "## Per-example sizes in complete valid suites", "",
              f"| n | Example | Tests | Mean size | Maximum | Tests >{ref} |", "|---:|---|---:|---:|---:|---:|"]
    for run in document["runs"]:
        for example, stats in run["by_example_rq5"].items():
            lines.append(f"| {run['n']} | {example} | {stats['count']} | {format_number(stats['mean'])} | {stats['max']} | {stats['above_reference']} |")
    lines += ["", f"## Tests larger than {ref} in complete valid suites", "",
              "| n | Example | Invariant | Test | Size |", "|---:|---|---|---|---:|"]
    lines += [f"| {r['n']} | {r['example']} | {r['invariant']} | {r['label']} | {r['maximum_atoms']} |"
              for r in tests if r["complete_valid_suite"] and r.get("above_reference")]
    lines += ["", "## Interpretation of the bounded optimum", "",
              "The original percentage of benchmark wrong specifications detected remains a useful empirical "
              "measure regardless of test scope. A best suite within a fixed scope is a bounded reference: "
              "an unrestricted LLM suite can exceed its detection count. Dividing LLM detection by that "
              "bounded optimum is not an unconditional percentage of the global optimum.", "",
              f"For a controlled comparison, use the suites entirely within {ref}, or recompute the optimum "
              "at a bound accommodating each suite. Keep the wrong-specification set, oracle, cumulative "
              "assumptions, suite size, and ordered-signature scope convention the same. The compared "
              "requirements should also be fixed across n if reporting a trend; historical RQ5 populations vary.", "",
              "## Reproduction", "", "```sh", "python analysis/scope_stats.py", "```", "",
              "`statistics.json` records input and JAR hashes, full summary populations, and distributions. "
              "`tests.csv` and `suites.csv` identify every test and suite. All existing experiment data are read-only.", ""]
    return "\n".join(lines)


def write_csv(path, rows):
    columns = list(dict.fromkeys(key for row in rows for key in row))
    with path.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=columns)
        writer.writeheader()
        writer.writerows({key: json.dumps(value, sort_keys=True) if isinstance(value, dict) else value
                         for key, value in row.items()} for row in rows)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("inputs", type=Path, nargs="*", help="execution JSON files; default: the five RQ5 runs")
    parser.add_argument("--jar", type=Path, default=ROOT / "alloytools.jar", help="Alloy 6 JAR")
    parser.add_argument("--failure-dir", type=Path, default=ROOT / "analysis/results")
    parser.add_argument("--output", type=Path, default=ROOT / "analysis/results/rq5_scopes")
    parser.add_argument("--reference-scope", type=int, default=4)
    args = parser.parse_args(argv)
    if args.reference_scope < 0:
        parser.error("--reference-scope must be nonnegative")
    paths = args.inputs or [ROOT / "execute/results" / (name + ".json") for name in RQ5_RUNS]
    import jpype
    import jpype.imports
    jpype.startJVM(classpath=[str(args.jar.resolve())])
    analyzer = ScopeAnalyzer()
    runs, tests, suites = [], [], []
    for path in paths:
        print(f"Measuring {path.name}...", flush=True)
        summary, run_tests, run_suites = analyze_run(path, args.failure_dir, analyzer, args.reference_scope)
        runs.append(summary)
        tests.extend(run_tests)
        suites.extend(run_suites)
        print(f"  {len(run_tests)} tests; {summary['historical_totals']['Complete']} complete valid suites", flush=True)
    document = {
        "generated_at": datetime.now(ZoneInfo("Europe/Lisbon")).isoformat(timespec="seconds"),
        "reference_scope": args.reference_scope,
        "jar": {"path": str(args.jar.resolve()), "sha256": digest(args.jar)},
        "script_sha256": digest(Path(__file__)), "runs": runs,
    }
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / "statistics.json").write_text(json.dumps(document, indent=2) + "\n")
    write_csv(args.output / "tests.csv", tests)
    write_csv(args.output / "suites.csv", suites)
    (args.output / "REPORT.md").write_text(report(document, tests, suites))
    print(f"Report: {args.output / 'REPORT.md'}")
    jpype.shutdownJVM()
    return 0


if __name__ == "__main__":
    sys.exit(main())
