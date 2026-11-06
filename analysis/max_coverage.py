"""Optional comparison with the exact optima saved by minimal/run_rates.py."""

import csv
import json
from pathlib import Path
import sys


BENCHMARK_NAMES = {
    "socialnetwork": "Photo sharing social network",
    "productionline": "Production line",
    "trainstation": "Train station",
    "courses": "Courses",
}


def within_scope(world, command, solution, bound, options):
    """Check every possible root population, rather than just the first witness."""
    from edu.mit.csail.sdg.parser import CompUtil
    from edu.mit.csail.sdg.translator import TranslateAlloyToKodkod

    overflow = None
    for sig in world.getAllReachableSigs():
        if (sig.builtin or not str(sig.label).startswith("this/")
                or not hasattr(sig, "parent") or str(sig.parent.label) != "univ"):
            continue
        if solution.eval(sig).size() > bound:
            return False
        names = ", ".join(f"coverageScopeAtom{i}" for i in range(bound + 1))
        at_least = CompUtil.parseOneExpression_fromString(
            world, f"some disj {names} : {sig.label} | no none")
        overflow = at_least if overflow is None else overflow.or_(at_least)
    if overflow is None:
        return True
    probe = command.change(command.formula.and_(overflow))
    larger = TranslateAlloyToKodkod.execute_command(None, world.getAllReachableSigs(), probe, options)
    return not larger.satisfiable()


class CoverageReference:
    def __init__(self, path):
        self.path = Path(path).resolve()
        data = json.loads(self.path.read_text())
        self.scope = data.get("scope_per_root")
        if type(self.scope) is not int or self.scope < 1:
            raise ValueError("Maximum-coverage results must record a positive scope_per_root.")
        if data.get("cumulative") is not True:
            raise ValueError("Maximum-coverage results must use cumulative requirements.")
        self.rows = {}
        for row in data["rows"]:
            if row.get("scope", self.scope) != self.scope:
                raise ValueError("Maximum-coverage results contain mixed scopes.")
            example = BENCHMARK_NAMES.get(row["example"], row["example"])
            key = (example, row["invariant"].split("/")[-1], row["n"])
            if key in self.rows:
                raise ValueError(f"Duplicate maximum-coverage result: {key}.")
            self.rows[key] = row
        snapshot = self.path.parent / "dataset.json"
        self.examples = {e["example"]: e for e in json.loads(snapshot.read_text())} if snapshot.exists() else {}

    def maximum(self, example, requirement, previous, n, considered):
        """Return an exact count, including a certified earlier 100% optimum."""
        key = (example["example"], requirement["pred"].split("/")[-1], n)
        row = self.rows.get(key)
        if row is None:
            raise ValueError(f"no result for n={n}")
        if row["description"] != requirement["description"] or row["total"] != len(requirement["erroneous"]):
            raise ValueError("requirement description or dataset total differs from the optimum")
        saved = self.examples.get(example["example"])
        if saved is not None:
            saved_req = saved["requirements"][row["R"]]
            saved_previous = [r["oracle"] for r in saved["requirements"][:row["R"]]]
            if (saved["model"].strip() != example["model"].strip()
                    or saved_req["pred"].split("/")[-1] != key[1]
                    or saved_req["oracle"].strip() != requirement["oracle"].strip()
                    or [r.strip() for r in saved_previous] != [r.strip() for r in previous]):
                raise ValueError("model, oracle, or earlier requirements differ from the optimum")
        if row["status"] == "skipped_100_percent":
            candidates = [r for (bench, inv, size), r in self.rows.items()
                          if (bench, inv) == key[:2] and size < n and r["status"] == "optimal"
                          and r["considered"] > 0 and r["detected"] == r["considered"]]
            if not candidates:
                raise ValueError("skipped size has no certified earlier 100% optimum")
            row = min(candidates, key=lambda r: r["n"])
        if row["status"] != "optimal":
            raise ValueError(f"optimum is unavailable ({row['status']})")
        if (row["total"] != len(requirement["erroneous"])
                or row["considered"] != row["total"] - row["unparseable"]
                or row["considered"] != considered):
            raise ValueError("parseable-specification totals differ from the optimum")
        maximum = row["detected"]
        if type(maximum) is not int or not 0 <= maximum <= considered:
            raise ValueError("invalid optimum detection count")
        return maximum

    def compare(self, example, requirement, previous, result, scoped):
        n = result["n"]
        complete = result["complete"] and scoped == result["generated"]
        comparison = dict(n=n, complete=bool(complete), maximum=None, percent=None)
        if not complete:
            return comparison
        try:
            maximum = self.maximum(example, requirement, previous, n, result["wrong"])
            detected = result["detected"]
            if detected > maximum:
                raise ValueError(f"suite detects {detected} specifications, exceeding the saved optimum {maximum}")
        except ValueError as exc:
            print(f"Warning: maximum-coverage comparison unavailable for {example['example']} "
                  f"{requirement['pred']} n={n}: {exc}.", file=sys.stderr)
            return comparison
        comparison.update(maximum=maximum, percent=100 * detected / maximum if maximum else None)
        return comparison

    def footer(self):
        return (
            f"**Maximum coverage:** reference [{self.path.name}]({self.path.as_posix()}), "
            f"scope **{self.scope}** per top-level domain. `n` is the requested number of tests "
            "per classification. "
            f"`Complete ≤{self.scope}` requires exactly n positive and n negative tests, all valid, "
            f"with every possible instance of each test using at most {self.scope} atoms per "
            "top-level domain under the declarations and earlier requirements. "
            "Actual populations are checked, rather than the command's declared upper bounds. "
            "`% of max` is 100 × detected wrong specifications / maximum detectable for the same n. "
            "Equivalent specification rewrites are accepted; model, oracle, cumulative requirements, "
            "and specification totals are cross-checked when the saved dataset is available. "
            "Skipped sizes use an earlier certified 100% result. "
            "Subtotals sum maximum counts and report the unweighted mean of per-suite percentages "
            "over complete suites within the reference scope. An unavailable comparison makes "
            "that subtotal unavailable. `—` denotes an ineligible suite, missing optimum, "
            "incompatible totals, or an undefined percentage when the optimum is zero."
        )


def comparison_cells(comparison):
    return [str(int(comparison["complete"])),
            str(comparison["maximum"]) if comparison["maximum"] is not None else "—",
            f"{comparison['percent']:.2f}" if comparison["percent"] is not None else "—"]


def comparison_total(comparisons):
    eligible = [c for c in comparisons if c["complete"]]
    known = bool(eligible) and all(c["maximum"] is not None for c in eligible)
    percentages = [c["percent"] for c in eligible if c["percent"] is not None]
    return dict(n=None, complete=len(eligible),
                maximum=sum(c["maximum"] for c in eligible) if known else None,
                percent=sum(percentages) / len(percentages) if known and percentages else None)


def append_comparison_columns(paths, results, scope):
    extra_rows, totals, overall = [], set(), []
    for requirements in results.values():
        comparisons = [r["max_coverage"] for r in requirements.values()]
        extra_rows.extend(comparison_cells(c) for c in comparisons)
        totals.add(len(extra_rows))
        extra_rows.append(comparison_cells(comparison_total(comparisons)))
        overall.extend(comparisons)
    totals.add(len(extra_rows))
    extra_rows.append(comparison_cells(comparison_total(overall)))
    for index, path in enumerate(paths):
        with open(path, newline="") as stream:
            rows = list(csv.reader(stream, delimiter="\t"))
        if len(rows) != len(extra_rows) + 1:
            raise ValueError("Summary rows do not match the maximum-coverage comparisons.")
        rows[0].extend([f"Complete ≤{scope}", "Max detected", "% of max"])
        for row_index, (row, cells) in enumerate(zip(rows[1:], extra_rows)):
            row.extend([f"**{cell}**" for cell in cells] if index == 0 and row_index in totals else cells)
        with open(path, "w", newline="") as stream:
            csv.writer(stream, delimiter="\t", lineterminator="\n").writerows(rows)
