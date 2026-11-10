#!/usr/bin/env python3
"""Run the remaining FAC27 experiments sequentially, or estimate their cost.

    python results/fac27/run_missing.py --estimate
    python results/fac27/run_missing.py --model terra --estimate
    python results/fac27/run_missing.py --model terra

Paths default to this experiment directory regardless of the working directory.
Estimation uses only local files and the Python standard library.
"""

import argparse
from collections import Counter
from contextlib import contextmanager
from dataclasses import dataclass
import hashlib
import json
import math
from pathlib import Path
import re
import subprocess
import sys
import time


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT))

from execute.generate import (
    COMPLETED_FIELDS, RESULT_FIELDS, default_output_path, load_resume_results, save_results,
)


MODELS = {
    "haiku": "claude-haiku-5-5",
    "luna": "gpt-6-luna",
    "flash-lite": "gemini-3.5-flash-lite",
    "sonnet": "claude-sonnet-5-5",
    "terra": "gpt-6.1-terra",
    "flash": "gemini-3.8-flash",
}
PLATFORMS = {model: ("claude-api" if model.startswith("claude") else
                     "gemini-api" if model.startswith("gemini") else "gpt-api")
             for model in MODELS.values()}
PROMPTS = (
    "prompt_zero", "prompt_one", "prompt_few",
    "prompt_zero_gpt", "prompt_one_gpt", "prompt_few_gpt", "prompt_few_json",
)
REPEATS = 3
RQ5_MODELS = frozenset(MODELS[name] for name in ("terra", "sonnet", "flash"))


@dataclass(frozen=True)
class Config:
    model: str
    prompt: str
    n: int = 3
    scope: int | None = None

    @property
    def mode(self):
        return "json" if self.prompt.endswith("_json") else "alloy"

    @property
    def label(self):
        return f"{self.model} {self.prompt} N={self.n} scope={self.scope or 'unbounded'}"


@dataclass
class Run:
    path: Path
    config: Config
    complete: bool
    input_tokens: float
    output_tokens: float


@dataclass
class Job:
    config: Config
    output: Path | None = None


def configurations(model=None):
    configs = []
    for selected in MODELS.values():
        if model is not None and selected != model:
            continue
        # Old/new prompts, RQ1/2, and unbounded JSON/repair cover all six models.
        configs.extend(Config(selected, prompt) for prompt in PROMPTS)
        if selected in RQ5_MODELS:
            configs.extend(Config(selected, "prompt_few_json", n, 4) for n in range(1, 6))
    return configs


def read_manifest(path):
    entries = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(entries, list):
        raise ValueError(f"{path}: expected a manifest list")
    seen = set()
    for entry in entries:
        if not isinstance(entry, dict) or not isinstance(entry.get("results"), str):
            raise ValueError(f"{path}: every entry must name a results file")
        result = (path.parent / entry["results"]).resolve()
        if result in seen:
            raise ValueError(f"Duplicate manifest entry: {result}")
        seen.add(result)
        for key in ("icost", "ocost"):
            if not valid_number(entry.get(key)):
                raise ValueError(f"{path}: invalid {key} for {result.name}")
    return entries


def valid_number(value):
    return type(value) in (int, float) and math.isfinite(value) and value >= 0


def read_run(path, dataset, prompt_hashes):
    # This verifies the model declarations, oracles, faults and requirement order.
    data = load_resume_results(path, dataset, result_fields=RESULT_FIELDS | {"json repair"})
    model = next((m for m in MODELS.values() if path.name.startswith(m + "_")), None)
    match = re.search(r"_(prompt_\w+?)_(\d+)pos-(\d+)neg(?:_|$)", path.stem)
    if model is None or match is None or match[1] not in PROMPTS:
        raise ValueError(f"Cannot identify the experiment in {path.name}")
    if match[2] != match[3]:
        raise ValueError(f"Positive/negative counts differ in {path.name}")
    prompt, count = match[1], int(match[2])
    scope_match = re.search(r"_scope(\d+)(?:_|$)", path.stem)
    filename_scope = int(scope_match[1]) if scope_match else None
    scopes, complete, input_tokens, output_tokens = set(), True, 0, 0
    for example in data:
        for req in example["requirements"]:
            generation = req.get("generation", {})
            settings = generation.get("settings", {})
            scope = settings.get("scope", filename_scope)
            if filename_scope is not None and scope != filename_scope:
                raise ValueError(f"{path.name}: filename and recorded scope disagree")
            # Untouched requirements in partial JSON checkpoints have no scope
            # metadata. Do not interpret those as completed unbounded results.
            if "scope" in settings or filename_scope is not None or COMPLETED_FIELDS.issubset(req):
                scopes.add(scope)
            expected_mode = "json" if prompt.endswith("_json") else "alloy"
            for key, expected in (("model", model), ("instances", count),
                                  ("platform", PLATFORMS[model]),
                                  ("prompt sha256", prompt_hashes[prompt])):
                if key in settings and settings[key] != expected:
                    raise ValueError(f"{path.name}: saved {key} disagrees with this experiment")
            if generation.get("mode", expected_mode) != expected_mode or "syntax repair" in req:
                raise ValueError(f"{path.name}: unexpected generation/repair mode")
            saved = (COMPLETED_FIELDS.issubset(req) and isinstance(req.get("instances"), str)
                     and valid_number(req.get("input tokens"))
                     and valid_number(req.get("output tokens")))
            if expected_mode == "json":
                # Exhausting the repair budget is an experimental outcome, not a missing run.
                state = req.get("json repair", {})
                saved = saved and state.get("complete") is True and state.get("max attempts") == 3
            complete = complete and saved
            input_tokens += req.get("input tokens", 0) if valid_number(req.get("input tokens", 0)) else 0
            output_tokens += req.get("output tokens", 0) if valid_number(req.get("output tokens", 0)) else 0
    if len(scopes) != 1:
        raise ValueError(f"{path.name}: inconsistent scopes between requirements")
    scope = scopes.pop()
    if scope is not None and (type(scope) is not int or scope < 1):
        raise ValueError(f"{path.name}: invalid maximum scope")
    return Run(path.resolve(), Config(model, prompt, count, scope), complete, input_tokens, output_tokens)


def load_history(manifest, dataset, prompt_hashes):
    entries, runs, rates = read_manifest(manifest), [], {}
    for entry in entries:
        run = read_run((manifest.parent / entry["results"]).resolve(), dataset, prompt_hashes)
        runs.append(run)
        price = (entry["icost"], entry["ocost"])
        if run.config.model in rates and rates[run.config.model] != price:
            raise ValueError(f"Conflicting token prices for {run.config.model} in {manifest}")
        rates[run.config.model] = price
    return runs, rates


def discover_unregistered(directory, history, configs, dataset, prompt_hashes):
    """Recover timestamped checkpoints, including a completed but unregistered run."""
    registered = {run.path for run in history}
    selected = set(configs)
    prefixes = {f"{c.model}_{PLATFORMS[c.model]}_{c.prompt}_" for c in configs}
    runs = []
    for path in sorted(directory.glob("*.json")):
        if path.resolve() in registered or not any(path.name.startswith(p) for p in prefixes):
            continue
        # Keep recognizing checkpoints from the runner's earlier naming scheme.
        if not re.search(r"_(?:\d{8}-\d{6}|fac27_rep\d+)\.json$", path.name):
            continue
        run = read_run(path, dataset, prompt_hashes)
        if run.config in selected:
            runs.append(run)
    return runs


def plan_jobs(configs, history, unregistered=()):
    jobs = []
    for config in configs:
        matching = [run for run in history if run.config == config]
        needed = max(0, REPEATS - sum(run.complete for run in matching))
        recoverable = [run for run in unregistered if run.config == config]
        recoverable.sort(key=lambda run: not run.complete)
        recoverable.extend(run for run in matching if not run.complete)
        recovered = recoverable[:needed]
        jobs.extend(Job(config, run.path) for run in recovered)
        jobs.extend(Job(config) for _ in range(needed - len(recovered)))
    return jobs


def new_output_path(config, directory):
    """Use the generator's default name, timestamped when this run starts."""
    while True:
        options = {"scope": config.scope} if config.mode == "alloy" else {}
        filename = default_output_path(config.model, PLATFORMS[config.model],
                                       Path(config.prompt + ".txt"), config.n, **options)
        output = (directory / filename).resolve()
        if not output.exists():
            return output
        # Never overwrite a run that started in the same second.
        time.sleep(1)


def estimate(config, history, rates):
    candidates = [r for r in history if r.complete and r.config.model == config.model
                  and r.config.mode == config.mode]
    alloy_proxy = not candidates and config.mode == "json"
    if alloy_proxy:
        candidates = [r for r in history if r.complete and r.config.model == config.model
                      and r.config.mode == "alloy"]
    if not candidates:
        raise ValueError(f"No comparable completed {config.mode} runs for {config.model}")
    target_prompt = "prompt_few_gpt" if alloy_proxy else config.prompt

    def distance(run):
        previous = run.config
        # Prefer the exact prompt; otherwise the same shot count in another version.
        shot = lambda prompt: prompt.split("_")[1]
        prompt_distance = (0 if previous.prompt == target_prompt else
                           1 if shot(previous.prompt) == shot(target_prompt) else 2)
        return (prompt_distance, previous.scope != config.scope, abs(previous.n - config.n))

    closest = min(map(distance, candidates))
    samples = [r for r in candidates if distance(r) == closest]
    icost, ocost = rates[config.model]
    # Input is largely fixed by the prompt and benchmark; output grows with suite size.
    cost = sum((r.input_tokens * icost + r.output_tokens * config.n / r.config.n * ocost)
               / 1_000_000 for r in samples) / len(samples)
    basis = samples[0].config
    description = (f"{len(samples)} prior {basis.prompt}, N={basis.n}, "
                   f"scope={basis.scope or 'unbounded'}")
    if alloy_proxy:
        description = "Alloy proxy, no JSON history; " + description
    if basis.n != config.n:
        description += f"; output scaled x{config.n / basis.n:.2f}"
    return cost, description


def print_plan(jobs, history, rates):
    print(f"Missing runs: {len(jobs)}")
    counts = Counter(job.config for job in jobs)
    total, model_totals = 0, {}
    for config, count in counts.items():
        cost, basis = estimate(config, history, rates)
        subtotal = count * cost
        total += subtotal
        old_count, old_cost = model_totals.get(config.model, (0, 0))
        model_totals[config.model] = old_count + count, old_cost + subtotal
        print(f"  {count} x {config.label}: ${subtotal:.4f} (~${cost:.4f}/run; {basis})")
    print("\nEstimated remaining cost (USD):")
    for model, (count, cost) in model_totals.items():
        print(f"  {model}: {count} runs, ${cost:.4f}")
    print(f"  TOTAL: {len(jobs)} runs, ${total:.4f}")
    if jobs:
        print("Estimates use manifest token prices and comparable completed runs. Input tokens "
              "stay fixed; output tokens scale with N when necessary. Scope/prompt fallbacks "
              "are shown above; estimates are approximate. JSON without prior same-model JSON "
              "runs uses a marked Alloy cost proxy; repair overhead is not separately predicted. "
              "Partial runs are priced as full runs.")


def command(job, dataset):
    if job.output is None:
        raise ValueError("Choose the output path before starting generation")
    config = job.config
    script = "generate_json.py" if config.mode == "json" else "generate.py"
    args = [sys.executable, str(ROOT / "execute" / script),
            str(ROOT / "prompts" / (config.prompt + ".txt")), str(dataset), str(config.n),
            "--model", config.model, "--platform", PLATFORMS[config.model], "-o", str(job.output)]
    if config.scope is not None:
        args.extend(["--scope", str(config.scope)])
    if config.mode == "json":
        args.extend(["--fix-attempts", "3", "--alloy-jar", str(ROOT / "alloytools.jar")])
    if job.output.exists():
        args.append("--resume")
    return args


def register_run(manifest, output, price):
    # Re-read before every atomic replacement to preserve entries added since startup.
    entries = read_manifest(manifest)
    if any((manifest.parent / e["results"]).resolve() == output.resolve() for e in entries):
        return
    entries.append({"results": str(output.relative_to(manifest.parent)),
                    "icost": price[0], "ocost": price[1]})
    save_results(manifest, entries)


@contextmanager
def execution_lock(manifest):
    import fcntl

    # A separate inode is needed because runs.json is replaced atomically.
    with (manifest.parent / ".run_missing.lock").open("a") as stream:
        try:
            fcntl.flock(stream, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise RuntimeError("Another FAC27 runner is already using this manifest.") from exc
        try:
            yield
        finally:
            fcntl.flock(stream, fcntl.LOCK_UN)


def execute_jobs(jobs, manifest, dataset_path, dataset, prompt_hashes, rates):
    for index, job in enumerate(jobs, 1):
        if job.output is None:
            job.output = new_output_path(job.config, manifest.parent)
        print(f"\n[{index}/{len(jobs)}] {job.config.label}\nOutput: {job.output}", flush=True)
        saved = read_run(job.output, dataset, prompt_hashes) if job.output.exists() else None
        if saved is not None and saved.config != job.config:
            raise ValueError(f"{job.output}: saved configuration differs from the planned run")
        if saved is None or not saved.complete:
            result = subprocess.run(command(job, dataset_path), cwd=ROOT)
            saved = read_run(job.output, dataset, prompt_hashes) if job.output.exists() else None
            if (result.returncode != 0 and not
                    (job.config.mode == "json" and result.returncode == 1
                     and saved is not None and saved.complete)):
                raise RuntimeError(f"Generation stopped (exit {result.returncode}). Re-run this "
                                   "script to resume its saved requirements; no manifest entry was added.")
        if saved is None or not saved.complete or saved.config != job.config:
            raise RuntimeError(f"{job.output}: generation did not finish the expected configuration")
        register_run(manifest, job.output, rates[job.config.model])
        print(f"Registered {job.output.name}", flush=True)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--model", choices=[*MODELS, *MODELS.values()],
                        help="run/estimate only this model (alias or full model ID)")
    parser.add_argument("--estimate", "--estimate-only", action="store_true",
                        help="print the missing runs and estimated USD cost; make no calls or writes")
    parser.add_argument("--manifest", type=Path, default=HERE / "runs.json")
    parser.add_argument("--dataset", type=Path, default=HERE / "dataset.json")
    args = parser.parse_args(argv)
    manifest, dataset_path = args.manifest.resolve(), args.dataset.resolve()
    try:
        dataset = json.loads(dataset_path.read_text(encoding="utf-8"))
        if not isinstance(dataset, list) or not dataset or not all(e.get("requirements") for e in dataset):
            raise ValueError("The dataset must contain nonempty benchmarks and requirements")
        hashes = {p: hashlib.sha256((ROOT / "prompts" / (p + ".txt")).read_text(
                  encoding="utf-8").encode()).hexdigest() for p in PROMPTS}
        selected = MODELS.get(args.model, args.model)

        def prepare():
            history, rates = load_history(manifest, dataset, hashes)
            configs = configurations(selected)
            unregistered = discover_unregistered(manifest.parent, history, configs, dataset, hashes)
            jobs = plan_jobs(configs, history, unregistered)
            for job in jobs:
                if job.config.model not in rates:
                    raise ValueError(f"No manifest prices for {job.config.model}")
                if job.output is not None and job.output.exists():
                    saved = read_run(job.output, dataset, hashes)
                    if saved.config != job.config:
                        raise ValueError(f"{job.output}: configuration differs from the planned run")
            print_plan(jobs, history, rates)
            return jobs, rates

        if args.estimate:
            prepare()
        else:
            with execution_lock(manifest):
                jobs, rates = prepare()
                execute_jobs(jobs, manifest, dataset_path, dataset, hashes, rates)
        return 0
    except KeyboardInterrupt:
        print("\nStopped. Re-run the same command to resume saved progress.", file=sys.stderr)
        return 130
    except (OSError, ValueError, RuntimeError, KeyError, TypeError) as exc:
        print(f"Error: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
