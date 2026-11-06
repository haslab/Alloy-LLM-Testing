"""Find an optimal bounded test suite for one of the four benchmark examples.

Usage: python minimal/optimal.py EXAMPLE R [n]
R is zero based; n defaults to one positive and one negative.
Every test satisfies requirements 0 through R-1.
"""

import argparse
from collections import Counter
from itertools import permutations, product
import json
from pathlib import Path
import sys
import tempfile

import jpype
import jpype.imports

from benchmarks import BENCHMARKS, DEFAULT_SCOPE, SOCIAL, translate

DIRECTORY = Path(__file__).resolve().parent

DATASET = DIRECTORY.parent / "prepare/results/dataset.json"
# Backwards-compatible names for callers of socialnetwork.py.
SIGNATURES = tuple(name for name, _ in SOCIAL.signatures)
RELATIONS = tuple(r.name for r in SOCIAL.relations)
DOMAINS = SOCIAL.domains
DECLARATIONS = SOCIAL.declarations


def nonnegative(value):
    value = int(value)
    if value < 0:
        raise argparse.ArgumentTypeError("must be a nonnegative integer")
    return value


def positive(value):
    value = int(value)
    if value < 1:
        raise argparse.ArgumentTypeError("must be at least 1")
    return value


def parse_args(argv=None, benchmark=None):
    parser = argparse.ArgumentParser(description=__doc__)
    if benchmark is None:
        parser.add_argument("example", choices=BENCHMARKS, help="benchmark example")
    parser.add_argument("R", type=nonnegative, help="zero-based requirement index")
    parser.add_argument(
        "n", nargs="?", default=1, type=nonnegative,
        help="number of positive AND negative tests (default: 1)",
    )
    parser.add_argument(
        "--jar", type=Path, default=DIRECTORY / "AlloyMax-1.0.2.jar",
        help="AlloyMax JAR (default: alongside this script)",
    )
    parser.add_argument(
        "--dataset", type=Path,
        default=DATASET,
        help="benchmark dataset (default: prepare/results/dataset.json)",
    )
    parser.add_argument(
        "--model-output", type=Path,
        help="also save the generated AlloyMax model to this file",
    )
    parser.add_argument(
        "--export-z3", type=Path, metavar="PATH",
        help="export PATH.smt2 and PATH.wcnf instead of optimizing with SAT4JMax",
    )
    parser.add_argument("--scope", type=positive, default=DEFAULT_SCOPE,
                        help="maximum atoms per top-level domain per test (default: 4)")
    parser.add_argument("--solver", choices=("sat4jmax", "z3"), default="sat4jmax",
                        help="optimizer backend (default: sat4jmax)")
    return parser.parse_args(argv)


def build_model(oracle, erroneous, n, exclusions=(), previous=(), benchmark=SOCIAL, scope=DEFAULT_SCOPE):
    oracle = translate(oracle, benchmark)
    erroneous = [translate(spec, benchmark) for spec in erroneous]
    previous = [translate(spec, benchmark) for spec in previous]
    background = "".join(
        f"    // Earlier requirement {i}, required in every Instance.\n{fact}\n"
        for i, fact in enumerate(previous)
    )
    semantics = [f"    Oracle in valid iff {oracle}"]
    semantics.extend(
        f"    S{i} in valid iff {spec}"
        for i, spec in enumerate(erroneous, 1)
    )
    formulas = ""
    if erroneous:
        formulas = "one sig " + ", ".join(
            f"S{i}" for i in range(1, len(erroneous) + 1)
        ) + " extends Formula {}\n"
    # Cardinalities here count Instance atoms, never Formula/detected atoms.
    bitwidth = benchmark.bitwidth(n, scope)
    scopes = [f"exactly {scope * len(benchmark.domains)} Atom"]
    scopes += [f"exactly {scope} {d}Atom" for d, _ in benchmark.domains]
    return (
        benchmark.render_declarations(scope) + background + "\n".join(semantics) + "\n}\n" + formulas
        + "\n".join(exclusions) + benchmark.render_helpers(scope)
        + f"""
run {{
    #valid.Oracle = {n}
    #(Instance - valid.Oracle) = {n}
    detected = {{ f : Formula - Oracle | valid.f != valid.Oracle }}
    maxsome detected
}} for {", ".join(scopes)},
       exactly {2 * n} Instance, {bitwidth} Int
"""
    )


def tuples(value):
    return [
        tuple(str(t.atom(i)) for i in range(t.arity()))
        for t in value
    ]


def extract_scenarios(solution, world, benchmark=SOCIAL, scope=DEFAULT_SCOPE):
    signatures = {str(s.label): s for s in world.getAllReachableSigs()}
    instance = signatures["this/Instance"]
    fields = {str(f.label): tuples(solution.eval(f)) for f in instance.getFields()}
    if benchmark.ordered:
        fields["grades"] = []
        for i in range(1, scope + 1):
            course = tuples(solution.eval(signatures[f"this/CourseSlot{i}"]))[0][0]
            fields["grades"] += [(inst, course, person, grade) for inst, person, grade in fields[f"grades{i}"]]
    oracle = tuples(solution.eval(signatures["this/Oracle"]))[0][0]
    positives = {i for i, f in fields["valid"] if f == oracle}
    scenarios = []
    for (atom,) in sorted(tuples(solution.eval(instance))):
        values = {
            name: sorted(t[1:] for t in fields[name] if t[0] == atom)
            for name in benchmark.names
        }
        scenarios.append((atom in positives, values))
    # A4TupleSet.size() counts in Java, independently of Alloy's Int bitwidth.
    detected_count = solution.eval(signatures["this/detected"]).size()
    return scenarios, detected_count


def atom_names(values, benchmark=SOCIAL):
    return {
        atom: f"{prefix}{i}"
        for domain, prefix in benchmark.domains
        for i, (atom,) in enumerate(values[domain], 1)
    }


def valuation(values, prefix="", benchmark=SOCIAL):
    """Complete valuation, usable in an output predicate or an Instance fact."""
    names = atom_names(values, benchmark)
    lines = []
    for domain, _ in benchmark.domains:
        if values[domain]:
            variables = ", ".join(names[a] for (a,) in values[domain])
            lines.append(f"some disj {variables} : {prefix}{domain} |")
    lines.append("{")
    for name in benchmark.names:
        relation = next((r for r in benchmark.relations if r.name == name), None)
        arity = len(relation.columns) if relation else 1
        output = name if prefix or relation is None else relation.output or name
        lhs = f"{prefix}{output}"
        if prefix and benchmark.ordered and name == "grades":
            lhs = f"instanceGrades[{prefix.rstrip('.')}]"
        rhs = " + ".join("->".join(names[a] for a in t) for t in values[name])
        lines.append(f"    {lhs} = {rhs or '->'.join(['none'] * arity)}")
    lines.append("}")
    return "\n".join(lines)


def canonical_key(values, benchmark=SOCIAL):
    """Canonicalize complete valuations using invariant colors before renaming.

    Color refinement and interchangeable atoms avoid enumerating scope!**domains
    permutations for the usual cases, without merging non-isomorphic scenarios.
    """
    signatures = tuple(name for name, _ in benchmark.signatures)
    memberships = {name: {a for (a,) in values[name]} for name in signatures}
    atoms = [a for domain, _ in benchmark.domains for (a,) in values[domain]]
    initial = {
        a: (index, tuple(a in memberships[name] for name in signatures))
        for index, (domain, _) in enumerate(benchmark.domains) for (a,) in values[domain]
    }
    ranks = {code: i for i, code in enumerate(sorted(set(initial.values())))}
    colors = {a: ranks[initial[a]] for a in atoms}
    relations = [set(values[r.name]) for r in benchmark.relations]
    while colors:
        neighbors = {a: [] for a in atoms}
        for index, relation in enumerate(relations):
            for row in relation:
                for column, atom in enumerate(row):
                    neighbors[atom].append((index, column, tuple(colors[a] for a in row),
                                            tuple(a == atom for a in row)))
        codes = {a: (colors[a], tuple(sorted(neighbors[a]))) for a in atoms}
        ranks = {code: i for i, code in enumerate(sorted(set(codes.values())))}
        refined = {a: ranks[codes[a]] for a in atoms}
        stable = len(set(refined.values())) == len(set(colors.values()))
        colors = refined
        if stable:
            break

    def interchangeable(group):
        # If every transposition fixes every relation, all renamings inside
        # this class give the same key, even with other classes held fixed.
        for other in group[1:]:
            swap = {group[0]: other, other: group[0]}
            if any({tuple(swap.get(a, a) for a in row) for row in relation} != relation
                   for relation in relations):
                return False
        return True

    classes, orders = [], []
    for domain, prefix in benchmark.domains:
        offset = 0
        for color in sorted({colors[a] for (a,) in values[domain]}):
            group = sorted(a for (a,) in values[domain] if colors[a] == color)
            classes.append((prefix, offset))
            orders.append([tuple(group)] if interchangeable(group) else permutations(group))
            offset += len(group)

    def key(groups):
        names = {a: f"{prefix}{offset + i}"
                 for (prefix, offset), group in zip(classes, groups) for i, a in enumerate(group)}
        return tuple(tuple(sorted(tuple(names[a] for a in row) for row in values[name]))
                     for name in benchmark.names)
    return min(key(groups) for groups in product(*orders))


def optimize(oracle, erroneous, n, model_output=None, previous=(), benchmark=SOCIAL, scope=DEFAULT_SCOPE, solver="sat4jmax"):
    from edu.mit.csail.sdg.parser import CompUtil
    from edu.mit.csail.sdg.translator import A4Options, TranslateAlloyToKodkod

    options = A4Options()
    options.solver = A4Options.SatSolver.SAT4JMax
    exclusions = []
    while True:
        model = build_model(oracle, erroneous, n, exclusions, previous, benchmark, scope)
        if model_output is not None:
            model_output.write_text(model, encoding="utf-8")
        world = CompUtil.parseEverything_fromString(None, model)
        if solver == "z3":
            from z3_backend import execute
            solution = execute(world, options, output_prefix=model_output)
        else:
            solution = TranslateAlloyToKodkod.execute_command(
                None, world.getAllReachableSigs(), world.getAllCommands()[0], options,
            )
        if not solution.satisfiable():
            # This AlloyMax version also makes maxsome require a nonempty set.
            # A feasible suite detecting zero specs is still a valid optimum.
            model = model.replace("    maxsome detected\n", "")
            if model_output is not None:
                model_output.write_text(model, encoding="utf-8")
            world = CompUtil.parseEverything_fromString(None, model)
            feasibility_options = A4Options()
            feasibility_options.solver = A4Options.SatSolver.SAT4J
            if solver == "z3":
                solution = execute(world, feasibility_options, output_prefix=model_output)
            else:
                solution = TranslateAlloyToKodkod.execute_command(
                    None, world.getAllReachableSigs(), world.getAllCommands()[0],
                    feasibility_options,
                )
        if not solution.satisfiable():
            raise ValueError(
                f"No suite with {n} distinct positive and {n} distinct negative "
                f"tests exists within scope {scope} per domain."
            )
        scenarios, count = extract_scenarios(solution, world, benchmark, scope)
        # Instance atoms can have isomorphic valuations. Forbid repeating each
        # such class, then reoptimize; no distinct suite is excluded by this.
        keys = [canonical_key(values, benchmark) for _, values in scenarios]
        repeated = {key for key, total in Counter(keys).items() if total > 1}
        if not repeated:
            return scenarios, count
        for key, (_, values) in zip(keys, scenarios):
            if key in repeated:
                exclusions.append(
                    "fact { lone { i : Instance |\n"
                    + valuation(values, "i.", benchmark) + "\n} }\n"
                )
                repeated.remove(key)
        print("Excluding repeated scenarios and reoptimizing...", file=sys.stderr)


def print_totals(total, unparseable, detected_count=None, status="not computed (export only)"):
    considered = total - unparseable
    print(f"// Total wrong specifications in dataset: {total}")
    print(f"// Unparseable wrong specifications skipped: {unparseable}")
    if detected_count is None:
        print(f"// Maximum wrong specifications detected: {status}")
        return
    print(f"// Maximum wrong specifications detected: {detected_count}/{considered}")
    if considered:
        ratio = detected_count / considered
        print(f"// Detection ratio among parseable specifications: {ratio:.6f} ({ratio:.2%})")
    else:
        print("// Detection ratio: N/A (no parseable wrong specifications)")


def print_suite(scenarios, detected_count, total, requirement, index, unparseable=0, benchmark=SOCIAL, scope=DEFAULT_SCOPE):
    description = " ".join(requirement["description"].split())
    bitwidth = benchmark.bitwidth(len(scenarios) // 2, scope)
    print(f"// Requirement {index}: {description}")
    if index:
        print(f"// All tests satisfy earlier requirements 0 through {index - 1}.")
    print_totals(total, unparseable, detected_count)
    print(f"// Maximum domain scope per test: {scope}")
    print(f"// Append to the {benchmark.key} declarations.")
    print("// expect assumes the target requirement is enforced as a fact.")
    print("// Both classes satisfy the declarations and earlier requirement facts.")
    for positive in (True, False):
        label = "Positive" if positive else "Negative"
        tests = [values for valid, values in scenarios if valid == positive]
        for i, values in enumerate(tests, 1):
            name = f"{label}Scenario{i}"
            result = "Satisfies" if positive else "Violates"
            print(f"\n// {result} the supplied oracle: {description}")
            print(f"pred {name} {{")
            print("\n".join("    " + line for line in valuation(values, benchmark=benchmark).splitlines()))
            print("}")
            scopes = ", ".join(f"exactly {len(values[d])} {d}" for d, _ in benchmark.domains)
            print(f"run {name} for {scopes}, {bitwidth} Int expect {int(positive)}")
    if not scenarios:
        print("// No scenarios requested.")


def wcnf_to_smt2(wcnf_path, smt2_path, comments=()):
    """Preserve hard/soft clauses with explicit names, without a Z3 dependency."""
    def literal(value):
        return f"d{value}" if value > 0 else f"(not d{-value})"

    with wcnf_path.open(encoding="utf-8") as source, smt2_path.open("w", encoding="utf-8") as out:
        header = next(line.split() for line in source if line.startswith("p "))
        if header[:2] != ["p", "wcnf"]:
            raise ValueError("Expected weighted DIMACS from AlloyMax")
        variables, expected_clauses, top = map(int, header[2:])
        out.write("; Weighted DIMACS exported by optimal.py\n")
        out.writelines(f"; {comment}\n" for comment in comments)
        out.write("(set-logic QF_LIA)\n")
        out.writelines(f"(declare-fun d{i} () Bool)\n" for i in range(1, variables + 1))
        terms = []
        clauses = 0
        for line in source:
            if not line.strip() or line.startswith("c"):
                continue
            weight, *values = map(int, line.split())
            if not values or values[-1] != 0 or 0 in values[:-1]:
                raise ValueError("Invalid clause in AlloyMax's weighted DIMACS output")
            values.pop()
            if any(abs(value) > variables for value in values):
                raise ValueError("DIMACS literal exceeds the declared variable count")
            body = (
                "false" if not values else literal(values[0]) if len(values) == 1
                else "(or " + " ".join(literal(value) for value in values) + ")"
            )
            if weight >= top:
                out.write(f"(assert {body})\n")
            else:
                out.write(f"(assert-soft {body} :weight {weight})\n")
                terms.append(f"(ite {body} {weight} 0)")
            clauses += 1
        if clauses != expected_clauses:
            raise ValueError("DIMACS clause count does not match its header")
        # The only objective is maxsome detected: one unit soft clause per
        # possible detected atom. Oracle is forced absent, so contributes zero.
        score = "0" if not terms else terms[0] if len(terms) == 1 else "(+ " + " ".join(terms) + ")"
        out.write(f"(define-fun detected_count () Int {score})\n")
        out.write("(check-sat)\n(get-value (detected_count))\n")


def export_z3(oracle, erroneous, n, destination, previous=(), model_output=None, comments=(), benchmark=SOCIAL, scope=DEFAULT_SCOPE):
    from edu.mit.csail.sdg.parser import CompUtil
    from edu.mit.csail.sdg.translator import A4Options, TranslateAlloyToKodkod

    # Check that n distinct tests of each class exist, without the expensive
    # detection objective. Then allowing repeated structures in the exported
    # assignment cannot change the maximum count: replace redundant copies
    # with unused distinct tests, retaining every original detection witness.
    optimize(oracle, [], n, previous=previous, benchmark=benchmark, scope=scope)
    model = build_model(oracle, erroneous, n, previous=previous, benchmark=benchmark, scope=scope)
    objective = "    maxsome detected\n"
    if erroneous and n:
        # maxsome also requires some detected atom in this AlloyMax version.
        # A plain SAT query determines whether any detection is possible.
        feasibility = CompUtil.parseEverything_fromString(None, model.replace(objective, "    some detected\n"))
        options = A4Options()
        options.solver = A4Options.SatSolver.SAT4J
        solution = TranslateAlloyToKodkod.execute_command(
            None, feasibility.getAllReachableSigs(), feasibility.getAllCommands()[0], options,
        )
        if not solution.satisfiable():
            model = model.replace(objective, "")
    else:
        model = model.replace(objective, "")
    if model_output is not None:
        model_output.write_text(model, encoding="utf-8")
    smt2_path = destination.with_suffix(".smt2").resolve()
    wcnf_path = destination.with_suffix(".wcnf").resolve()
    with tempfile.TemporaryDirectory(prefix=f"{benchmark.key}-export-") as directory:
        options = A4Options()
        options.solver = A4Options.SatSolver.WCNF
        options.tempDirectory = directory
        world = CompUtil.parseEverything_fromString(None, model)
        TranslateAlloyToKodkod.execute_command(
            None, world.getAllReachableSigs(), world.getAllCommands()[0], options,
        )
        files = list(Path(directory).glob("*.wcnf"))
        if len(files) != 1:
            raise ValueError("AlloyMax did not produce exactly one WCNF file")
        text = files[0].read_text(encoding="utf-8")
    if text.startswith("p cnf "):
        # AlloyMax writes ordinary CNF for trivially SAT/UNSAT problems,
        # even when WCNF was requested. Normalize those all-hard clauses.
        header, *clauses = text.splitlines()
        _, _, variables, count = header.split()
        text = f"p wcnf {variables} {count} 1\n" + "".join(f"1 {clause}\n" for clause in clauses)
    wcnf_path.write_text("".join(f"c {comment}\n" for comment in comments) + text, encoding="utf-8")
    wcnf_to_smt2(wcnf_path, smt2_path, comments)
    return smt2_path, wcnf_path


def main(argv=None, benchmark=None):
    args = parse_args(argv, benchmark)
    benchmark = benchmark or BENCHMARKS[args.example]
    total = None
    erroneous = []
    try:
        dataset = json.loads(args.dataset.read_text(encoding="utf-8"))
        example = dataset[benchmark.index]
        if example["model"].strip() != benchmark.original.strip():
            raise ValueError(f"Dataset declarations differ from the supported {benchmark.key} model")
        if args.R >= len(example["requirements"]):
            raise ValueError(f"R must be between 0 and {len(example['requirements']) - 1}")
        requirement = example["requirements"][args.R]
        previous = [req["oracle"] for req in example["requirements"][:args.R]]
        if not args.jar.is_file():
            raise ValueError(f"AlloyMax JAR not found: {args.jar}")
        if not jpype.isJVMStarted():
            jpype.startJVM(classpath=[str(args.jar.resolve())])
        from edu.mit.csail.sdg.parser import CompUtil

        background_model = example["model"] + "\n" + "\n".join(
            f"fact {{{oracle}}}" for oracle in previous
        )
        # A malformed background is an error, not a reason to skip every spec.
        CompUtil.parseEverything_fromString(None, background_model)
        total = len(requirement["erroneous"])
        for spec in requirement["erroneous"]:
            try:
                CompUtil.parseEverything_fromString(
                    None, background_model + f"\nfact {{{spec}}}",
                )
            except jpype.JException:
                continue
            erroneous.append(spec)
        print(
            f"{'Exporting' if args.export_z3 else 'Optimizing'} "
            f"{args.n} positive and {args.n} negative tests against "
            f"{len(erroneous)} parseable wrong specifications "
            f"with {len(previous)} earlier requirements enforced, scope {args.scope}, solver {args.solver}...", file=sys.stderr,
        )
        if args.export_z3:
            description = " ".join(requirement["description"].split())
            comments = [
                f"Requirement {args.R}: {description}",
                f"Dataset: {args.dataset.resolve()}",
                f"Positive tests: {args.n}; negative tests: {args.n}",
                f"Earlier requirement facts enforced: {len(previous)}",
                f"Scope per top-level domain: {args.scope}",
                f"Total wrong specifications: {total}; unparseable: {total - len(erroneous)}; considered: {len(erroneous)}",
                "The optimum detected_count is also attainable with distinct tests.",
            ]
            smt2, wcnf = export_z3(
                requirement["oracle"], erroneous, args.n, args.export_z3,
                previous, args.model_output, comments, benchmark, args.scope,
            )
            print(f"// Requirement {args.R}: {description}")
            print_totals(total, total - len(erroneous))
            print(f"// Exported Z3 SMT-LIB: {smt2}")
            print(f"// Exported weighted DIMACS: {wcnf}")
            return 0
        scenarios, count = optimize(
            requirement["oracle"], erroneous, args.n, args.model_output, previous, benchmark, args.scope, args.solver,
        )
        print(f"// Dataset: {args.dataset.resolve()}")
        print(f"// Optimizer backend: {args.solver}")
        print_suite(scenarios, count, total, requirement, args.R, total - len(erroneous), benchmark, args.scope)
        return 0
    except (OSError, ValueError, jpype.JException) as exc:
        if total is not None:
            print_totals(total, total - len(erroneous), status="unavailable (optimization failed)")
        print(f"Error: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
