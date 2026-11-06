"""Generate JSON valuations and translate validated instances into Alloy tests."""

import argparse
import copy
import hashlib
import json
from pathlib import Path
import sys

if __package__:
    from .generate import (RESULT_FIELDS, build_task, call_with_retries, default_output_path,
                           load_resume_results, positive_int, save_results)
    from .model_client import ModelClient, PLATFORMS
    from .syntax_repair import AlloySyntaxChecker
    from .valuation import ValuationError, ValuationModel, decode_response, valuation_key
else:
    from generate import (RESULT_FIELDS, build_task, call_with_retries, default_output_path,
                          load_resume_results, positive_int, save_results)
    from model_client import ModelClient, PLATFORMS
    from syntax_repair import AlloySyntaxChecker
    from valuation import ValuationError, ValuationModel, decode_response, valuation_key


JSON_RESULT_FIELDS = RESULT_FIELDS | {"json repair"}
DEFAULT_JAR = Path(__file__).resolve().parents[1] / "alloytools.jar"
CLASSIFICATIONS = ("positive", "negative")
VALIDATION_VERSION = 2
FEEDBACK_VERSION = 2
REPAIR_SYSTEM_PROMPT = """You repair concrete JSON valuations for an Alloy model.
Return only one valid JSON object with exactly two keys, positive and negative,
each mapping to an array. Return only the replacement counts requested in the
repair task, in the given original-slot order; an unrequested class is [].
Each valuation has exactly explanation (a short string), signatures (an object
mapping every user signature to its atom-identifier array), and fields (an object
mapping every 'DeclaringSignature <: field' key to its array of tuples).
Include empty signatures and fields explicitly as []. Respect the supplied
inventory and tuple arities; do not invent signatures, fields, atoms, or keys.
Subsignatures reuse parent atoms. Every referenced user atom must be present in
its top-level signature. Both classifications must satisfy the supplied model's
declarations and facts and the required earlier natural language requirements.
Positive instances satisfy the current natural language requirement; negative
instances violate it. Edit the supplied failed valuations using the feedback,
preserving correct values wherever possible. Retained instances are read-only
context and must not be returned or duplicated. Do not formalize requirements,
generate Alloy code, add Markdown fences, or put prose outside the JSON object.
"""


def nonnegative_int(value):
    number = int(value)
    if number < 0:
        raise argparse.ArgumentTypeError("must be a nonnegative integer")
    return number


def parse_args(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("prompt", type=Path, help="JSON-oriented header prompt, e.g. prompt_few_json.txt")
    parser.add_argument("dataset", type=Path, help="JSON dataset of natural language requirements")
    parser.add_argument("instances", type=positive_int, help="number of positive AND negative instances")
    parser.add_argument("--model", required=True, help="concrete model ID (used to infer the API)")
    parser.add_argument("--platform", choices=PLATFORMS, help="override API inference")
    parser.add_argument("--codex-exec", default="codex", help="Codex CLI command or app path")
    parser.add_argument("--scope", type=nonnegative_int,
                        help="optional maximum atoms per top-level signature (default: no imposed maximum)")
    parser.add_argument("--alloy-jar", type=Path, default=DEFAULT_JAR, help="Alloy jar for model inspection and compilation")
    parser.add_argument("--ollama-format", choices=("schema", "json", "none"), default="schema",
                        help="Ollama constrained output: model-derived schema (default), JSON only, or none")
    parser.add_argument("-o", "--output", type=Path, help="output JSON path (default: model/platform/prompt/count/date)")
    parser.add_argument("--resume", action="store_true", help="resume an existing explicit --output file")
    parser.add_argument("--attempts", type=positive_int, default=3,
                        help="maximum transport attempts per request (default: 3)")
    parser.add_argument("--fix-attempts", type=nonnegative_int, default=3,
                        help="maximum batched JSON repair queries per requirement (default: 3; 0 disables repairs)")
    args = parser.parse_args(argv)
    if args.resume and args.output is None:
        parser.error("--resume requires an explicit --output path")
    return args


def task_prompt(example, requirement, previous, count, model):
    population = (
        f"Maximum scope: {model.scope} atoms per top-level signature. "
        "Use any smaller population, including zero, where permitted.\n"
        if model.scope is not None else
        "No maximum scope is specified. Prefer small populations, including zero where permitted.\n"
    )
    return (
        build_task(example["model"], requirement["description"], previous, count)
        + "\n\n" + population
        + "Required signature and field inventory (field tuple arities include the owning atom):\n"
        + json.dumps(model.inventory(), indent=2)
        + f"\nReturn JSON with exactly {count} positive and {count} negative valuations, "
        "using the format in the header prompt."
    )


def _slot(classification, index):
    return f"{classification}{index}"


def _suite(accepted, count):
    return "\n\n".join(accepted[key]["instances"] for classification in CLASSIFICATIONS
                         for index in range(1, count + 1)
                         if (key := _slot(classification, index)) in accepted)


def _targets(accepted, count):
    return {classification: [index for index in range(1, count + 1)
                             if _slot(classification, index) not in accepted]
            for classification in CLASSIFICATIONS}


def assess_response(model, record, accepted):
    """Validate requested slots independently and keep earlier passing valuations."""
    targets = record["targets"]
    failures = {}
    record["warnings"] = []
    record.pop("valuations", None)
    try:
        payload = decode_response(record["response"])
        record["valuations"] = payload
        if not isinstance(payload, dict):
            raise ValueError("Return an object with positive and negative arrays.")
        extra_keys = set(payload) - set(CLASSIFICATIONS)
        if extra_keys:
            raise ValueError(f"Unknown top-level keys: {sorted(extra_keys)}. Use only positive and negative.")
    except ValueError as exc:
        return {_slot(kind, index): [f"Invalid JSON response: {exc}"]
                for kind, indices in targets.items() for index in indices}

    existing = {valuation_key(entry["valuation"]) for entry in accepted.values()}
    for classification, indices in targets.items():
        entries = payload.get(classification)
        if not isinstance(entries, list):
            for index in indices:
                failures[_slot(classification, index)] = [f"{classification} must be an array of {len(indices)} valuations."]
            continue
        if len(entries) > len(indices):
            record["warnings"].append(
                f"{classification}: received {len(entries)} valuations, requested {len(indices)}; "
                "surplus entries were retained in the raw response and excluded from the final suite."
            )
        for position, index in enumerate(indices):
            key = _slot(classification, index)
            if position >= len(entries):
                failures[key] = [f"Missing {classification} valuation for slot {index}."]
                continue
            instance = entries[position]
            try:
                command = model.render(instance, classification, index)
                model.check_consistency(instance, command)
                canonical = valuation_key(instance)
                if canonical in existing:
                    raise ValuationError(["This valuation duplicates an already retained instance; produce a distinct valuation."])
            except ValuationError as exc:
                failures[key] = list(dict.fromkeys(exc.errors + model.declaration_feedback(instance)))
                continue
            accepted[key] = {"valuation": instance, "instances": command}
            existing.add(canonical)
    return failures


def repair_prompt(task, accepted, errors, targets, record):
    retained = {key: entry["valuation"] for key, entry in accepted.items()}
    # A repair array's position maps through that response's original target
    # slots. In a later round, positive[0] may mean positive3, not positive1.
    rejected = {}
    payload = record.get("valuations")
    if isinstance(payload, dict) and any(isinstance(payload.get(kind), list) for kind in CLASSIFICATIONS):
        for classification, indices in targets.items():
            source_indices = record["targets"].get(classification, [])
            entries = payload.get(classification)
            for index in indices:
                position = source_indices.index(index) if index in source_indices else None
                present = isinstance(entries, list) and position is not None and position < len(entries)
                rejected[_slot(classification, index)] = (
                    {"valuation": entries[position]} if present else
                    {"missing": True, "instruction": "Supply a new valuation for this slot."}
                )
    if rejected:
        faulty = "Current rejected valuations by original slot (edit these valuations):\n" + json.dumps(rejected, indent=2)
    else:
        # Decoding failures still need the actual faulty input. Do not discard
        # duplicate keys or silently repair JSON before the model sees it.
        faulty = "The latest response could not be interpreted as valuation arrays. Repair this exact raw response:\n" + record["response"]
    return (
        f"Original task:\n{task}\n\n"
        "Repair or supply only the missing or invalid JSON valuations listed below. "
        "Preserve the requested classification, satisfy the same requirement and earlier constraints, "
        "and use the same scope and declaration inventory. Edit the supplied rejected valuations "
        "rather than inventing a replacement suite. Preserve correct entries and values unless a "
        "reported error or model constraint requires a change. Do not generate Alloy code.\n"
        + faulty + "\n\n"
        + f"Feedback by original slot:\n{json.dumps(errors, indent=2)}\n"
        "Already retained valuations (read-only context; do not return or duplicate them):\n"
        + json.dumps(retained, indent=2)
        + "\nFor THIS repair response, return one object with positive and negative arrays. "
        f"The positive array must contain exactly {len(targets['positive'])} valuations, "
        f"replacing original slots {targets['positive']} in that order. "
        f"The negative array must contain exactly {len(targets['negative'])} valuations, "
        f"replacing original slots {targets['negative']} in that order. "
        "An array with no requested slots must be []. Each valuation must contain exactly "
        "explanation, signatures, and fields, in the same JSON format as the original task."
    )


def _upgrade_validation(state):
    version = state.get("validation version", 1)
    if version > VALIDATION_VERSION:
        raise ValueError("The saved run uses a newer JSON validation version.")
    if version == VALIDATION_VERSION:
        return
    state.setdefault("validation history", []).append(copy.deepcopy({
        key: state[key] for key in ("accepted", "errors", "complete", "successful", "processed responses", "max attempts")
        if key in state
    }) | {"version": version})
    state["accepted"] = {}
    state["errors"] = {}
    state["processed responses"] = 0
    state["validation version"] = VALIDATION_VERSION


def _archive_assessment(record):
    if record.get("validation version") == VALIDATION_VERSION:
        return
    if "errors" in record:
        record.setdefault("validation history", []).append({
            "version": record.get("validation version", 1),
            "errors": copy.deepcopy(record["errors"]), "instances": record.get("instances", ""),
        })
    record["validation version"] = VALIDATION_VERSION


def _response_format(client, model, targets, mode):
    if client.platform != "ollama" or mode == "none":
        return None
    if mode == "json":
        return "json"
    return model.response_schema(len(targets["positive"]), len(targets["negative"]))


def _record(response, targets, cache, response_format=None):
    record = {"response": response.text, "targets": targets,
              "input tokens": response.input_tokens, "output tokens": response.output_tokens}
    if cache:
        record["cached input tokens"] = response.cached_input_tokens
    if response_format is not None:
        record["response format"] = response_format
    return record


def _add_usage(requirement, record):
    for field in ("input tokens", "output tokens", "cached input tokens"):
        if field in record:
            requirement[field] = requirement.get(field, 0) + record[field]


def generate_json_instances(client, system_prompt, dataset, models, count, settings, *,
                            attempts=3, fix_attempts=3, output=None, resume=False, ollama_format="schema"):
    successful = True

    def checkpoint():
        if output is not None:
            save_results(output, dataset)

    for example, model in zip(dataset, models):
        print(f"========================================\n{example['example']}\n========================================")
        previous = []
        for requirement in example["requirements"]:
            print(requirement["description"])
            task = task_prompt(example, requirement, previous, count, model)
            if not resume or "generation" not in requirement:
                targets = {kind: list(range(1, count + 1)) for kind in CLASSIFICATIONS}
                response_format = _response_format(client, model, targets, ollama_format)
                response = call_with_retries(client, system_prompt, task, attempts,
                                             f"JSON generation failed for {example['example']}: {requirement['description']}",
                                             response_format=response_format)
                for field in JSON_RESULT_FIELDS:
                    requirement.pop(field, None)
                record = _record(response, targets, client.platform == "codex-cli", response_format)
                record.update({"mode": "json", "settings": settings})
                record["prompt"] = task
                requirement["generation"] = record
                requirement["instances"] = ""
                _add_usage(requirement, record)
                requirement["json repair"] = {"rounds": [], "accepted": {}, "processed responses": 0,
                                              "validation version": VALIDATION_VERSION}
                checkpoint()
            state = requirement["json repair"]
            _upgrade_validation(state)
            accepted = state["accepted"]
            state["max attempts"] = fix_attempts
            state["complete"] = False
            # Recheck saved valuations without calling the model, and rebuild the
            # commands using the same renderer and validated run settings.
            for key, entry in accepted.items():
                match = parse_slot(key)
                if match is None or not 1 <= match[1] <= count:
                    raise ValueError(f"Invalid saved JSON valuation slot: {key}")
                entry["instances"] = model.render(entry["valuation"], *match)
                model.check_consistency(entry["valuation"], entry["instances"])
            while True:
                records = [requirement["generation"], *state["rounds"]]
                while state["processed responses"] < len(records):
                    record = records[state["processed responses"]]
                    _archive_assessment(record)
                    state["errors"] = assess_response(model, record, accepted)
                    record["errors"] = state["errors"]
                    record["instances"] = requirement["instances"] = _suite(accepted, count)
                    state["processed responses"] += 1
                    checkpoint()
                targets = _targets(accepted, count)
                if not any(targets.values()) or len(state["rounds"]) >= fix_attempts:
                    state["complete"] = True
                    state["successful"] = not any(targets.values())
                    requirement["instances"] = _suite(accepted, count)
                    successful &= state["successful"]
                    checkpoint()
                    if not state["successful"]:
                        print(f"Unresolved JSON valuations after {len(state['rounds'])} repair queries: "
                              f"{list(state['errors'])}", file=sys.stderr)
                    break
                fix_task = repair_prompt(task, accepted, state["errors"], targets, records[-1])
                response_format = _response_format(client, model, targets, ollama_format)
                response = call_with_retries(
                    client, REPAIR_SYSTEM_PROMPT, fix_task, attempts,
                    f"JSON repair failed for {example['example']}: {requirement['description']}",
                    response_format=response_format,
                )
                record = _record(response, targets, client.platform == "codex-cli", response_format)
                record.update({"prompt": fix_task, "system prompt": REPAIR_SYSTEM_PROMPT,
                               "feedback version": FEEDBACK_VERSION})
                state["rounds"].append(record)
                _add_usage(requirement, record)
                # Save the response and cost before validation, so a crash during
                # compilation can resume without issuing or charging that call again.
                checkpoint()
            previous.append(requirement["description"])
    return successful


def parse_slot(key):
    for kind in CLASSIFICATIONS:
        if isinstance(key, str) and key.startswith(kind) and key[len(kind):].isdigit():
            return kind, int(key[len(kind):])
    return None


def _resume_settings_match(saved, current):
    if not isinstance(saved, dict):
        return False
    normalized = dict(saved)
    # Older runs sent no native format. They can still be resumed explicitly
    # with --ollama-format none, without relabeling their previous requests.
    normalized.setdefault("ollama format", "none" if saved.get("platform") == "ollama" else None)
    return normalized == current


def main(argv=None):
    args = parse_args(argv)
    try:
        client = ModelClient(args.model, args.platform, args.codex_exec)
        prompt = args.prompt.read_text(encoding="utf-8")
        dataset = json.loads(args.dataset.read_text(encoding="utf-8"))
        output = args.output or default_output_path(client.model, client.platform, args.prompt, args.instances)
        if output.resolve() in (args.dataset.resolve(), args.prompt.resolve(), args.alloy_jar.resolve()):
            raise ValueError("The output must differ from the dataset, prompt, and Alloy jar paths.")
        if not output.parent.is_dir() or output.is_dir():
            raise ValueError("Choose an output file in an existing directory.")
        checker = AlloySyntaxChecker(args.alloy_jar)
        settings = {"version": 1, "model": client.model, "platform": client.platform,
                    "prompt sha256": hashlib.sha256(prompt.encode()).hexdigest(),
                    "instances": args.instances, "scope": args.scope,
                    "alloy sha256": hashlib.sha256(args.alloy_jar.read_bytes()).hexdigest(),
                    "ollama format": args.ollama_format if client.platform == "ollama" else None}
        if args.resume:
            dataset = load_resume_results(output, dataset, result_fields=JSON_RESULT_FIELDS)
            for example in dataset:
                for requirement in example["requirements"]:
                    if "generation" in requirement:
                        record = requirement["generation"]
                        if record.get("mode") != "json" or not _resume_settings_match(record.get("settings"), settings):
                            raise ValueError("Resume settings differ: use the same JSON mode, model, platform, prompt contents, instance count, scope, Alloy jar, and Ollama format. Older Ollama runs require --ollama-format none; use a new output file to try schema mode.")
                        if "json repair" not in requirement:
                            raise ValueError("The saved JSON generation is missing its repair state.")
                    elif "instances" in requirement:
                        raise ValueError("This output contains results from another generation mode; choose a JSON-mode output file.")
        else:
            for example in dataset:
                for requirement in example["requirements"]:
                    for field in JSON_RESULT_FIELDS:
                        requirement.pop(field, None)
        models = [ValuationModel(example["model"], args.scope, checker) for example in dataset]
        scope_description = args.scope if args.scope is not None else "not specified"
        print(f"Model: {client.model}; platform: {client.platform}; JSON mode; maximum scope: {scope_description}")
        if client.platform == "ollama":
            print(f"Ollama format: {args.ollama_format}")
        print(f"Output: {output}")
        successful = generate_json_instances(
            client, prompt, dataset, models, args.instances, settings, attempts=args.attempts,
            fix_attempts=args.fix_attempts, output=output, resume=args.resume,
            ollama_format=args.ollama_format,
        )
        save_results(output, dataset)
        print(f"Saved results to {output}")
        return 0 if successful else 1
    except (OSError, ValueError, RuntimeError) as exc:
        print(f"Error: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
