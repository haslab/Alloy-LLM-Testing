"""Run all invariants for n=1..5, stopping each invariant at 100% detection.

Results and concrete suites are checkpointed after each case. Use --output DIR
--resume to continue an interrupted run with the saved dataset and source.
"""

import argparse
from collections import Counter, deque
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import csv
from datetime import datetime
import fcntl
import hashlib
import io
import json
import os
from pathlib import Path
import platform
import re
import shutil
import signal
import subprocess
import sys
import threading
import time
from zoneinfo import ZoneInfo

from benchmarks import BENCHMARKS, DEFAULT_SCOPE


DIRECTORY = Path(__file__).resolve().parent
DATASET = DIRECTORY.parent / "prepare/results/dataset.json"
ZONE = ZoneInfo("Europe/Lisbon")
CSV_COLUMNS = (
    "example", "invariant", "R", "n", "scope", "solver", "status", "total", "unparseable", "considered",
    "detected", "ratio", "percent", "elapsed_seconds", "source_revision", "suite", "log", "model", "error",
)
CHILDREN = set()
CHILDREN_LOCK = threading.Lock()
STOP = threading.Event()
SNAPSHOT_FILES = ("optimal.py", "benchmarks.py", "run_rates.py", "z3_backend.py",
                  "java/edu/mit/csail/sdg/translator/Z3Bridge.java")


def now():
    return datetime.now(ZONE).isoformat(timespec="seconds")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def positive(value):
    value = int(value)
    if value < 1:
        raise argparse.ArgumentTypeError("must be at least 1")
    return value


def arguments(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="results directory (default: timestamped directory in minimal/results)")
    parser.add_argument("--dataset", type=Path, default=DATASET)
    parser.add_argument("--jar", type=Path, default=DIRECTORY / "AlloyMax-1.0.2.jar")
    parser.add_argument("--jobs", type=positive, default=2, help="simultaneous solver processes (default: 2)")
    parser.add_argument("--max-n", type=positive, default=5)
    parser.add_argument("--timeout", type=positive, help="optional limit in seconds per case; default: no time limit")
    parser.add_argument("--scope", type=positive, default=DEFAULT_SCOPE,
                        help="maximum atoms per top-level domain per test (default: 4)")
    parser.add_argument("--solver", choices=("sat4jmax", "z3"), default="sat4jmax")
    parser.add_argument("--resume", action="store_true", help="resume using the dataset/source saved in --output")
    parser.add_argument("--retry-failed", action="store_true", help="with --resume, also retry errors/timeouts")
    parser.add_argument("--refresh-source", action="store_true", help="with --resume, archive saved source and adopt current optimizer fixes")
    args = parser.parse_args(argv)
    if (args.resume or args.retry_failed) and args.output is None:
        parser.error("--resume/--retry-failed requires --output")
    if args.retry_failed and not args.resume:
        parser.error("--retry-failed requires --resume")
    if args.refresh_source and not args.resume:
        parser.error("--refresh-source requires --resume")
    return args


def atomic_write(path, text):
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(text, encoding="utf-8")
    temporary.replace(path)


def parse_result(stdout, stderr, returncode, expected_total, n):
    """Read exact counts, rather than the rounded percentage printed by the CLI."""
    result = {"total": expected_total}
    for key, pattern in [
        ("total", r"^// Total wrong specifications in dataset: (\d+)$"),
        ("unparseable", r"^// Unparseable wrong specifications skipped: (\d+)$"),
    ]:
        match = re.search(pattern, stdout, re.MULTILINE)
        if match:
            result[key] = int(match[1])
    if result["total"] != expected_total:
        raise ValueError(f"Dataset total mismatch: expected {expected_total}, received {result['total']}")
    if "unparseable" in result:
        result["considered"] = result["total"] - result["unparseable"]
        if not 0 <= result["considered"] <= result["total"]:
            raise ValueError("Invalid skipped-specification count")
    if returncode:
        infeasible = re.search(r"Error: No suite with \d+ distinct positive and \d+ distinct negative tests exists", stderr)
        result.update(status="infeasible" if infeasible else "error", error=stderr.strip()[-2000:])
        return result
    match = re.search(r"^// Maximum wrong specifications detected: (\d+)/(\d+)$", stdout, re.MULTILINE)
    if not match or "considered" not in result:
        raise ValueError("Solver output is missing exact detection/skipped counts")
    detected, considered = map(int, match.groups())
    if considered != result["considered"] or not 0 <= detected <= considered:
        raise ValueError("Inconsistent detection totals in solver output")
    if any(stdout.count(f"pred {kind}Scenario") != n for kind in ("Positive", "Negative")):
        raise ValueError("Solver output has the wrong number of positive/negative scenarios")
    ratio = detected / considered if considered else None
    result.update(status="optimal", detected=detected, ratio=ratio,
                  percent=100 * ratio if ratio is not None else None, error="")
    return result


def initialize(output, args):
    if args.resume:
        state = json.loads((output / "results.json").read_text())
        if args.scope != state["scope_per_root"]:
            raise ValueError(f"Resume requires --scope {state['scope_per_root']}; use a new directory for another scope")
        expected_solver = "z3" if state["solver"] == "Z3" else "sat4jmax"
        if args.solver != expected_solver:
            raise ValueError(f"Resume requires --solver {expected_solver}")
        for relative, expected in state["files"].items():
            if digest(output / relative) != expected:
                raise ValueError(f"Saved input/source changed: {relative}")
        if digest(Path(state["jar"])) != state["jar_sha256"]:
            raise ValueError("AlloyMax JAR has changed since this run started")
        revision = state.setdefault("source_revision", 1)
        for row in state["rows"]:
            if row["attempt"]:
                row.setdefault("source_revision", revision)
        if args.refresh_source:
            archive = Path("source-history") / f"revision{revision}"
            (output / archive).mkdir(parents=True, exist_ok=True)
            previous = {}
            for relative in state["files"]:
                if relative.startswith("source/"):
                    name = Path(relative).relative_to("source")
                    (output / archive / name).parent.mkdir(parents=True, exist_ok=True)
                    shutil.copyfile(output / relative, output / archive / name)
                    previous[str(archive / name)] = state["files"][relative]
            for name in SNAPSHOT_FILES:
                target = output / "source" / name
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(DIRECTORY / name, target)
                state["files"]["source/" + name] = digest(target)
            state.setdefault("source_history", []).append(dict(revision=revision, files=previous, archived_at=now()))
            state["source_revision"] += 1
        for row in state["rows"]:
            if row["status"] in ("running", "interrupted") or (
                args.retry_failed and row["status"] in ("error", "timeout", "blocked_by_error")
            ):
                row.setdefault("attempt_history", []).append({k: v for k, v in row.items() if k != "attempt_history"})
                row["status"] = "pending"
        state["resumed_at"] = now()
    else:
        if (output / "results.json").exists():
            raise ValueError("Results already exist; use --resume or a new --output directory")
        (output / "source").mkdir(parents=True, exist_ok=True)
        shutil.copyfile(args.dataset, output / "dataset.json")
        for name in SNAPSHOT_FILES:
            target = output / "source" / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(DIRECTORY / name, target)
        dataset = json.loads((output / "dataset.json").read_text())
        rows = []
        for b in BENCHMARKS.values():
            example = dataset[b.index]
            if example["model"].strip() != b.original.strip():
                raise ValueError(f"Unsupported declarations for {b.key}")
            for index, requirement in enumerate(example["requirements"]):
                for n in range(1, args.max_n + 1):
                    rows.append({
                        "example": b.key, "invariant": requirement.get("pred", f"inv{index + 1}").split("/")[-1],
                        "R": index, "n": n, "scope": args.scope, "solver": args.solver, "status": "pending", "total": len(requirement["erroneous"]),
                        "description": requirement["description"], "attempt": 0,
                    })
        files = ["dataset.json"] + ["source/" + name for name in SNAPSHOT_FILES]
        state = {
            "started_at": now(), "dataset_original": str(args.dataset.resolve()),
            "files": {name: digest(output / name) for name in files},
            "jar": str(args.jar.resolve()), "jar_sha256": digest(args.jar),
            "python": sys.version, "platform": platform.platform(), "max_n": args.max_n,
            "scope_per_root": args.scope, "solver": "Z3" if args.solver == "z3" else "SAT4JMax", "cumulative": True,
            "ratio_denominator": "parseable wrong specifications", "source_revision": 1, "rows": rows,
        }
    state.update(status="running", pid=os.getpid(), jobs=args.jobs, timeout_seconds=args.timeout)
    if state["solver"] == "Z3":
        try:
            import z3
        except ImportError as exc:
            raise ValueError("--solver z3 requires the z3-solver Python package") from exc
        state["z3_version"] = z3.get_version_string()
    return state


def cell(row):
    status = row["status"]
    if status == "optimal":
        if row["ratio"] is None:
            return "N/A (no parseable specs)"
        return f"{row['percent']:.2f}% ({row['detected']}/{row['considered']})"
    if status.startswith("skipped_"):
        return "— (" + row["reason"] + ")"
    return {"infeasible": "no suite", "blocked_by_error": "blocked by earlier error"}.get(status, status)


def checkpoint(output, state):
    state["updated_at"] = now()
    atomic_write(output / "results.json", json.dumps(state, indent=2) + "\n")
    csv_text = io.StringIO(newline="")
    writer = csv.DictWriter(csv_text, fieldnames=CSV_COLUMNS, extrasaction="ignore")
    writer.writeheader()
    writer.writerows(state["rows"])
    atomic_write(output / "results.csv", csv_text.getvalue())
    counts = Counter(r["status"] for r in state["rows"])
    text = [
        "# Optimal test-suite detection rates", "",
        f"Status: **{state['status']}**. Updated: {state['updated_at']}.", "",
        "Dataset: [saved dataset](dataset.json); source: [source/](source/).",
        f"Solver: {state.get('solver', 'SAT4JMax')}. Cumulative requirements. Bound: {state.get('scope_per_root', DEFAULT_SCOPE)} atoms per top-level domain. "
        f"Each n requests n positive and n negative, structurally distinct tests.", "",
        "Rates use parseable wrong specs as the denominator. Counts are obtained in Java, "
        "without Alloy's cardinality operator. Higher n are skipped only after exact "
        "100% coverage, zero parseable specs, or proven suite infeasibility. "
        "Errors/timeouts leave higher n blocked, never reported as optimal.", "",
        "Cases: " + ", ".join(f"{status}: {count}" for status, count in sorted(counts.items())) + ".", "",
        "See [results.csv](results.csv) for timings, totals, skipped counts, and artifact paths; "
        "[results.json](results.json) also records input hashes, commands, and errors.", "",
        "| Example | Invariant (R) | Dataset total | Unparseable | "
        + " | ".join(f"n={n}" for n in range(1, state["max_n"] + 1)) + " |",
        "|---|---|---:|---:|" + "---|" * state["max_n"],
    ]
    groups = {}
    for row in state["rows"]:
        groups.setdefault((row["example"], row["R"]), []).append(row)
    aggregate = []
    for n in range(1, state["max_n"] + 1):
        reached, unresolved, infeasible = 0, 0, 0
        for rows in groups.values():
            full = any(r["status"] == "optimal" and r["n"] <= n and r["considered"] > 0
                       and r["detected"] == r["considered"] for r in rows)
            reached += full
            impossible = any(r["status"] == "infeasible" and r["n"] <= n for r in rows)
            infeasible += impossible
            known = any(r["n"] == n and r["status"] == "optimal" for r in rows)
            unresolved += not (full or impossible or known)
        aggregate.append(dict(n=n, reached_100=reached, unresolved=unresolved, infeasible=infeasible))
    heading = text.index("| Example | Invariant (R) | Dataset total | Unparseable | "
                         + " | ".join(f"n={n}" for n in range(1, state["max_n"] + 1)) + " |")
    overview = ["Invariants reaching 100% at n or earlier (counts are lower bounds while cases remain unresolved):", "",
                "| n | Reached 100% | Unresolved | Infeasible |", "|---:|---:|---:|---:|"]
    overview += [f"| {r['n']} | {'≥' if r['unresolved'] else ''}{r['reached_100']} | {r['unresolved']} | {r['infeasible']} |"
                 for r in aggregate]
    text[heading:heading] = overview + [""]
    aggregate_csv = io.StringIO(newline="")
    aggregate_writer = csv.DictWriter(aggregate_csv, fieldnames=list(aggregate[0]))
    aggregate_writer.writeheader()
    aggregate_writer.writerows(aggregate)
    atomic_write(output / "aggregate.csv", aggregate_csv.getvalue())
    for rows in groups.values():
        first = rows[0]
        skipped = next((r["unparseable"] for r in rows if "unparseable" in r), "—")
        text.append(f"| {first['example']} | {first['invariant']} ({first['R']}) | {first['total']} | {skipped} | "
                    + " | ".join(cell(r) for r in rows) + " |")
    text.append("")
    if state.get("source_history"):
        text += ["Optimizer source was revised during this run. Previous source is archived in "
                 "[source-history/](source-history/); each result records its source revision and "
                 "previous attempts in results.json.", ""]
    atomic_write(output / "SUMMARY.md", "\n".join(text))


def run_case(output, state, row):
    started = time.monotonic()
    command = [sys.executable, str(output / "source/optimal.py"), row["example"], str(row["R"]), str(row["n"]),
               "--dataset", str(output / "dataset.json"), "--jar", state["jar"],
               "--model-output", str(output / row["model"]), "--scope", str(state["scope_per_root"]),
               "--solver", "z3" if state["solver"] == "Z3" else "sat4jmax"]
    result = {"command": command, "started_at": now()}
    try:
        with (output / row["suite"]).open("w") as stdout, (output / row["log"]).open("w") as stderr:
            with CHILDREN_LOCK:
                if STOP.is_set():
                    return {"status": "interrupted"}
                process = subprocess.Popen(command, stdout=stdout, stderr=stderr, start_new_session=True)
                CHILDREN.add(process)
            try:
                returncode = process.wait(timeout=state["timeout_seconds"])
            except subprocess.TimeoutExpired:
                process.terminate()
                try:
                    process.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    process.kill()
                    process.wait()
                result.update(status="timeout", error=f"Exceeded {state['timeout_seconds']} seconds; optimum not determined")
            finally:
                with CHILDREN_LOCK:
                    CHILDREN.discard(process)
        if "status" not in result:
            result.update(parse_result((output / row["suite"]).read_text(), (output / row["log"]).read_text(),
                                       returncode, row["total"], row["n"]))
            result["returncode"] = returncode
    except (OSError, ValueError) as exc:
        result.update(status="error", error=str(exc))
    result.update(finished_at=now(), elapsed_seconds=round(time.monotonic() - started, 3))
    return result


def next_case(rows):
    """Apply the exact-count stopping rule and return the next runnable n."""
    for index, row in enumerate(rows):
        status = row["status"]
        if status == "pending":
            return row
        if status == "optimal":
            if row["considered"] and row["detected"] != row["considered"]:
                continue
            stop = "skipped_100_percent" if row["considered"] else "skipped_no_parseable_specs"
            reason = f"100% at n={row['n']}" if row["considered"] else "no parseable specs"
        elif status == "infeasible":
            stop, reason = "skipped_infeasible", f"infeasible at n={row['n']}"
        elif status in ("error", "timeout", "blocked_by_error"):
            stop, reason = "blocked_by_error", f"{status} at n={row['n']}"
        else:
            return None
        for later in rows[index + 1:]:
            if later["status"] == "pending":
                later.update(status=stop, reason=reason)
        return None
    return None


def execute(output, state, worker=run_case):
    STOP.clear()
    groups = {}
    for row in state["rows"]:
        groups.setdefault((row["example"], row["R"]), []).append(row)
    # Breadth first: run every invariant's n=1 before newly queued larger n.
    queue = deque(row for rows in groups.values() if (row := next_case(rows)) is not None)
    active = {}
    pool = ThreadPoolExecutor(max_workers=state["jobs"])
    checkpoint(output, state)
    try:
        while queue or active:
            while queue and len(active) < state["jobs"]:
                row = queue.popleft()
                row.update(status="running", attempt=row["attempt"] + 1, source_revision=state.get("source_revision", 1))
                directory = Path("cases") / row["example"] / row["invariant"]
                (output / directory).mkdir(parents=True, exist_ok=True)
                stem = directory / f"n{row['n']}.attempt{row['attempt']}"
                row.update(suite=f"{stem}.suite.als", log=f"{stem}.log", model=f"{stem}.model.als")
                print(f"{now()} START {row['example']} {row['invariant']} (R={row['R']}) n={row['n']}", flush=True)
                active[pool.submit(worker, output, state, row)] = row
            checkpoint(output, state)
            finished, _ = wait(active, timeout=30, return_when=FIRST_COMPLETED)
            for future in finished:
                row = active.pop(future)
                try:
                    result = future.result()
                except Exception as exc:
                    result = {"status": "error", "error": repr(exc)}
                rows = groups[row["example"], row["R"]]
                earlier = rows[:row["n"] - 1]
                if result["status"] == "optimal" and earlier and (
                    result["considered"] != earlier[-1]["considered"]
                    or result["detected"] < earlier[-1]["detected"]
                ):
                    result.update(status="error", error="Detection count decreased or denominator changed; check encoding")
                row.update(result)
                print(f"{now()} DONE {row['example']} {row['invariant']} n={row['n']}: {cell(row)} "
                      f"({row.get('elapsed_seconds', 0):.1f}s)", flush=True)
                following = next_case(rows)
                if following is not None:
                    queue.append(following)
        failures = any(r["status"] in ("error", "timeout", "blocked_by_error") for r in state["rows"])
        state.update(status="completed_with_errors" if failures else "completed", finished_at=now())
        return 1 if failures else 0
    except BaseException:
        STOP.set()
        with CHILDREN_LOCK:
            for process in CHILDREN:
                process.terminate()
        for row in active.values():
            row["status"] = "interrupted"
        state["status"] = "interrupted"
        raise
    finally:
        pool.shutdown(wait=True, cancel_futures=True)
        checkpoint(output, state)


def main(argv=None):
    args = arguments(argv)
    output = (args.output or DIRECTORY / "results" / datetime.now(ZONE).strftime("detection-rates-%Y%m%d-%H%M%S")).resolve()
    output.mkdir(parents=True, exist_ok=True)
    with (output / ".lock").open("a") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            print(f"Another runner is already using {output}", file=sys.stderr)
            return 1
        try:
            state = initialize(output, args)
            def stop(signum, frame):
                raise KeyboardInterrupt
            signal.signal(signal.SIGTERM, stop)
            print(f"Results: {output}", flush=True)
            return execute(output, state)
        except KeyboardInterrupt:
            print("Interrupted; checkpoint saved. Resume with --output DIR --resume.", file=sys.stderr)
            return 130
        except (OSError, ValueError) as exc:
            print(f"Error: {exc}", file=sys.stderr)
            return 1


if __name__ == "__main__":
    sys.exit(main())
