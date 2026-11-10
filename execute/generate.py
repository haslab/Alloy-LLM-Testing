"""Generate Alloy instances using a model ID and an inferred API transport."""

import argparse
import hashlib
import json
import os
import re
import sys
import tempfile
import time
from datetime import datetime
from pathlib import Path

if __package__:
    from .model_client import CacheUsageError, ModelClient, PLATFORMS
    from .syntax_repair import AlloySyntaxChecker, repair_suite
else:
    from model_client import CacheUsageError, ModelClient, PLATFORMS
    from syntax_repair import AlloySyntaxChecker, repair_suite


RESULT_FIELDS = {"instances", "input tokens", "output tokens", "cached input tokens",
                 "generation", "syntax repair"}
COMPLETED_FIELDS = {"instances", "input tokens", "output tokens"}


def positive_int(value: str) -> int:
    number = int(value)
    if number < 1:
        raise argparse.ArgumentTypeError("must be a positive integer")
    return number


def parse_args(argv=None, default_model=None):
    parser = argparse.ArgumentParser(description="Generate Alloy instances using a selected model")
    parser.add_argument("prompt", type=Path, help="header prompt to be passed to the model")
    parser.add_argument("dataset", type=Path, help="JSON dataset of natural language requirements")
    parser.add_argument("instances", type=positive_int, help="number of positive and negative instances")
    parser.add_argument("--model", required=default_model is None, default=default_model,
                        help="concrete model ID (used to infer the API)")
    parser.add_argument("--platform", choices=PLATFORMS,
                        help="override API inference; use codex-cli for ChatGPT subscription access")
    parser.add_argument("--codex-exec", default="codex",
                        help="Codex CLI command or path (default: PATH, then macOS app bundles)")
    parser.add_argument("-o", "--output", type=Path,
                        help="output JSON path (default: MODEL_PLATFORM_PROMPT_COUNT_DATE.json)")
    parser.add_argument("--resume", action="store_true",
                        help="resume saved results from an existing --output file")
    parser.add_argument("--attempts", type=positive_int, default=3,
                        help="maximum transport attempts per model request (default: 3)")
    parser.add_argument("--scope", type=positive_int,
                        help="request at most this many atoms per top-level signature")
    parser.add_argument("--repair-syntax", type=Path, metavar="ALLOY_JAR",
                        help="check each instance with Alloy and batch parser feedback to repair failures")
    parser.add_argument("--fix-attempts", type=positive_int, default=3,
                        help="maximum repair queries per requirement (default: 3)")
    args = parser.parse_args(argv)
    if args.resume and args.output is None:
        parser.error("--resume requires an explicit --output path")
    return args


def default_output_path(model: str, platform: str, prompt: Path, instances: int, scope=None) -> Path:
    components = [
        re.sub(r"[^A-Za-z0-9_.-]", "_", component.strip())
        for component in (model, platform, prompt.stem)
    ]
    count = f"{instances}pos-{instances}neg"
    timestamp = datetime.now().strftime("%Y%m%d-%H%M%S")
    bound = [f"scope{scope}"] if scope is not None else []
    return Path("_".join([*components, count, *bound, timestamp]) + ".json")


def build_task(model: str, requirement: str, previous: list[str], instances: int, scope=None) -> str:
    # Keep the prompts identical to those used by the original experiment scripts.
    task = (
        f'Generate {instances} positive and {instances} negative instances for the '
        f'requirement "{requirement}" for the following model.'
    )
    if len(previous) == 1:
        task += f' All instances must also satisfy the requirement "{previous[0]}".'
    elif len(previous) > 1:
        task += ' All instances must also satisfy the requirements'
        for description in previous[:-1]:
            task += f'"{description}",'
        task += f'and "{previous[-1]}".'
    task += f"\n{model}"
    if scope is not None:
        task += (
            f"\n\nMaximum scope: {scope} atoms per top-level signature, including all its extensions. "
            "Use any smaller population, including zero, where permitted by the model. "
            "Specify exact command scopes matching the chosen populations; no top-level "
            "signature may exceed this maximum. An ordered signature's exact scope must "
            "match its actual population and may be smaller than the maximum."
        )
    return task


def save_results(output: Path, dataset):
    """Replace the checkpoint only after the complete JSON has been written."""
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w", encoding="utf-8", dir=output.parent,
            prefix=f".{output.name}.", suffix=".tmp", delete=False,
        ) as stream:
            temporary = Path(stream.name)
            json.dump(dataset, stream, indent=4)
            stream.write("\n")
            stream.flush()
            os.fsync(stream.fileno())
        temporary.replace(output)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def load_resume_results(output: Path, dataset, *, result_fields=None):
    """Accept saved results only for the same dataset and requirement order."""
    saved = json.loads(output.read_text(encoding="utf-8"))
    ignored = RESULT_FIELDS if result_fields is None else result_fields

    def without_results(data):
        if not isinstance(data, list):
            raise TypeError("expected a dataset list")
        return [
            {**example, "requirements": [
                {key: value for key, value in requirement.items() if key not in ignored}
                for requirement in example["requirements"]
            ]}
            for example in data
        ]

    try:
        matches = without_results(saved) == without_results(dataset)
    except (AttributeError, KeyError, TypeError):
        matches = False
    if not matches:
        raise ValueError("The resume output does not match the dataset or requirement order.")
    return saved


def call_with_retries(client, system_prompt, task, attempts, context, *, response_format=None):
    for attempt in range(1, attempts + 1):
        try:
            options = {"response_format": response_format} if response_format is not None else {}
            return client.call(system_prompt, task, **options)
        except CacheUsageError:
            raise
        except Exception as exc:
            if attempt == attempts:
                raise RuntimeError(
                    f"{context} after {attempts} attempt(s). {exc}"
                ) from exc
            print(f"Attempt {attempt}/{attempts} failed: {exc}; retrying.", file=sys.stderr)
            time.sleep(min(2 ** (attempt - 1), 30))


def generation_settings(client, prompt, count, jar=None, scope=None):
    return {
        "version": 1,
        "model": client.model if isinstance(getattr(client, "model", None), str) else None,
        "platform": client.platform if isinstance(getattr(client, "platform", None), str) else None,
        "prompt sha256": hashlib.sha256(prompt.encode()).hexdigest(),
        "instances": count, "scope": scope,
        "alloy sha256": hashlib.sha256(jar.read_bytes()).hexdigest() if jar else None,
    }


def generate_instances(client, system_prompt, dataset, instances, attempts=3, *,
                       output=None, resume=False, syntax_checker=None, fix_attempts=3, settings=None):
    settings = settings or generation_settings(client, system_prompt, instances)
    if resume:
        for example in dataset:
            for requirement in example["requirements"]:
                generation = requirement.get("generation", {})
                if generation.get("mode") not in (None, "alloy"):
                    raise ValueError("The saved run uses another generation mode.")
                saved_settings = generation.get("settings", {})
                has_saved_result = "generation" in requirement or COMPLETED_FIELDS.issubset(requirement)
                if has_saved_result and saved_settings.get("scope") != settings.get("scope"):
                    raise ValueError("Resume settings differ: scope. Use the original generation settings.")
                for key in ("instances", "model", "platform", "prompt sha256"):
                    if saved_settings.get(key) is not None and saved_settings[key] != settings[key]:
                        raise ValueError(f"Resume settings differ: {key}. Use the original generation settings.")
    for example in dataset:
        print("========================================")
        print(example["example"])
        print("========================================")
        if syntax_checker is not None:
            syntax_checker.validate_model(example["model"])
        previous = []
        for requirement in example["requirements"]:
            print(requirement["description"])
            saved = (resume and COMPLETED_FIELDS.issubset(requirement)
                     and isinstance(requirement["instances"], str))
            if saved and "instances" not in requirement.get("generation", {}).get("settings", {}):
                generation = requirement.setdefault("generation", {})
                generation.setdefault("settings", {})["instances"] = instances
                generation.setdefault("metadata source", "Requested count supplied when resuming a legacy run.")
            if saved and syntax_checker is None:
                print("Skipping saved result.")
                previous.append(requirement["description"])
                continue
            task = build_task(example["model"], requirement["description"], previous, instances,
                              scope=settings.get("scope"))

            def checkpoint():
                if output is not None:
                    save_results(output, dataset)

            if not saved:
                response = call_with_retries(
                    client, system_prompt, task, attempts,
                    f"Generation failed for {example['example']}: {requirement['description']}",
                )
                blocks = re.findall(r"```alloy(.*?)```", response.text, re.DOTALL)
                requirement["instances"] = "\n".join(blocks) if blocks else response.text
                requirement["input tokens"] = response.input_tokens
                requirement["output tokens"] = response.output_tokens
                if client.platform == "codex-cli":
                    requirement["cached input tokens"] = response.cached_input_tokens
                # A fresh run must not reuse history from an annotated dataset.
                requirement.pop("generation", None)
                requirement.pop("syntax repair", None)
                requirement["generation"] = {
                    key: requirement[key] for key in
                    ("instances", "input tokens", "output tokens", "cached input tokens")
                    if key in requirement
                }
                requirement["generation"].update({
                    "mode": "alloy", "settings": dict(settings), "prompt": task,
                    "response": response.text,
                    "targets": {kind: list(range(1, instances + 1)) for kind in ("positive", "negative")},
                })
                checkpoint()
            if syntax_checker is not None:
                # Legacy files may contain only backfilled count metadata.
                generation = requirement["generation"]
                for field in ("instances", "input tokens", "output tokens", "cached input tokens"):
                    if field in requirement:
                        generation.setdefault(field, requirement[field])
                def request(fix_task):
                    return call_with_retries(
                        client, system_prompt, fix_task, attempts,
                        f"Syntax repair failed for {example['example']}: {requirement['description']}",
                    )

                repair_suite(
                    syntax_checker, requirement, example["model"], task, request,
                    max_attempts=fix_attempts, checkpoint=checkpoint,
                )
                state = requirement["syntax repair"]
                if state["successful"]:
                    print(f"All instances compile; repair queries: {len(state['rounds'])}.")
                else:
                    print(
                        f"{len(state['errors'])} instance(s) still fail syntax checks after "
                        f"{len(state['rounds'])} repair query/queries; saved for analysis.",
                        file=sys.stderr,
                    )
            previous.append(requirement["description"])
    return dataset


def main(argv=None, default_model=None):
    args = parse_args(argv, default_model)
    try:
        client = ModelClient(args.model, args.platform, args.codex_exec)
        system_prompt = args.prompt.read_text(encoding="utf-8")
        dataset = json.loads(args.dataset.read_text(encoding="utf-8"))
        output = args.output or default_output_path(
            client.model, client.platform, args.prompt, args.instances, scope=args.scope,
        )
        if output.resolve() in (args.dataset.resolve(), args.prompt.resolve()):
            raise ValueError("The output path must differ from the dataset and prompt paths.")
        if not output.parent.is_dir() or output.is_dir():
            raise ValueError("Choose an output file in an existing directory.")
        if args.resume:
            dataset = load_resume_results(output, dataset)
        syntax_checker = AlloySyntaxChecker(args.repair_syntax) if args.repair_syntax else None
        print(f"Model: {client.model}; platform: {client.platform}")
        print(f"Output: {output}")
        result = generate_instances(
            client, system_prompt, dataset, args.instances, args.attempts,
            output=output, resume=args.resume, syntax_checker=syntax_checker,
            fix_attempts=args.fix_attempts,
            settings=generation_settings(client, system_prompt, args.instances, args.repair_syntax,
                                         scope=args.scope),
        )
        save_results(output, result)
        print(f"Saved results to {output}")
    except (OSError, ValueError, RuntimeError) as exc:
        print(f"Error: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
