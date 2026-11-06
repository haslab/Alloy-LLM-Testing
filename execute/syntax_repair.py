"""Optional Alloy compiler feedback and batched repair of generated run commands."""

import re


TRIVIA = re.compile(r'"(?:\\.|[^"\\])*"|//[^\n]*|--[^\n]*|/\*[\s\S]*?(?:\*/|$)')
RUN = re.compile(r"\brun\b")
EXPECT = re.compile(r"\bexpect\s+([01])\b")
DECLARATION = re.compile(r"\b(?:sig|enum|fact|pred|fun|assert|open|module|check)\b")
FENCES = re.compile(r"```[^\n`]*\n(.*?)```", re.DOTALL)


def mask_trivia(source):
    """Hide comments and strings without changing offsets or line numbers."""
    def mask(match):
        replacement = "~" if match.group().startswith('"') else " "
        return "".join("\n" if char == "\n" else replacement for char in match.group())

    return TRIVIA.sub(mask, source)


def split_instances(source):
    """Keep malformed commands, including missing braces or expect clauses."""
    masked = mask_trivia(source)
    starts = [match.start() for match in RUN.finditer(masked)]
    if not starts:
        return [source.strip()]
    # Attach comments between commands to the following command. Unlike the
    # analysis regex, splitting does not require a syntactically valid ending.
    boundaries = [0, *(len(masked[:start].rstrip()) for start in starts[1:]), len(source)]
    return [source[start:end].strip() for start, end in zip(boundaries, boundaries[1:])]


def replacement_instances(response):
    blocks = FENCES.findall(response)
    if blocks:
        return [candidate for block in blocks for candidate in split_instances(block)]
    return split_instances(response)


class AlloySyntaxChecker:
    def __init__(self, jar):
        if not jar.is_file():
            raise ValueError(f"Alloy jar does not exist: {jar}")
        try:
            import jpype
            import jpype.imports
        except ImportError as exc:
            raise RuntimeError("Syntax repair requires JPype. Install requirements.txt.") from exc
        if not jpype.isJVMStarted():
            try:
                jpype.startJVM(classpath=[str(jar.resolve())])
            except (OSError, RuntimeError) as exc:
                raise RuntimeError(f"Could not start Java for Alloy syntax repair: {exc}") from exc
        try:
            self.parse = jpype.JClass("edu.mit.csail.sdg.parser.CompUtil").parseEverything_fromString
            self.error = jpype.JClass("edu.mit.csail.sdg.alloy4.Err")
        except (TypeError, RuntimeError) as exc:
            raise RuntimeError(f"Could not load the Alloy parser from {jar}: {exc}") from exc

    def validate_model(self, model):
        try:
            self.parse(None, model)
        except self.error as exc:
            raise ValueError(f"The original Alloy model does not compile: {exc}") from exc

    def feedback(self, model, candidate, expected=None):
        masked = mask_trivia(candidate)
        if len(RUN.findall(masked)) != 1 or not masked.lstrip().startswith("run"):
            return "Return exactly one run command, with no prose or additional commands."
        if DECLARATION.search(masked):
            return "Return only the run command; do not add or change model declarations, facts, or predicates."
        try:
            world = self.parse(None, model + "\n" + candidate)
        except self.error as exc:
            offset = (model + "\n").count("\n")
            line = int(exc.pos.y) - offset
            location = f"Instance line {line}, column {exc.pos.x}" if line > 0 else "Model error"
            return f"{location}: {exc.msg}"
        commands = list(world.getAllCommands())
        # The datasets contain declarations only; do not rely on Alloy's implicit
        # default command when an actual generated command is missing.
        command = commands[-1]
        if command.check or command.expects not in (0, 1):
            return "The run command must explicitly end with expect 0 or expect 1."
        if expected is not None and command.expects != expected:
            return f"Preserve the original classification: this command must end with expect {expected}."
        return None


def repair_prompt(task, entries, feedback):
    problems = []
    for issue in feedback:
        entry = entries[issue["instance"] - 1]
        expected = entry["expect"]
        classification = f"Keep expect {expected}." if expected is not None else "Include expect 0 or expect 1."
        problems.append(
            f"Instance {issue['instance']}. {classification}\n"
            f"```alloy\n{entry['instances']}\n```\nCompiler feedback:\n{issue['error']}"
        )
    return (
        f"Original generation task:\n{task}\n\n"
        "Repair the following failed Alloy instances using the compiler feedback. "
        "Change only what is needed to fix syntax, name resolution, or typing. "
        "Preserve each intended concrete instance and its positive/negative classification. "
        "Do not formalize the natural language requirements or add declarations, facts, or predicates. "
        "Each command must work independently with the original model.\n\n"
        + "\n\n".join(problems)
        + f"\n\nReturn exactly {len(feedback)} fenced alloy code block(s), one complete run command "
        "per block, in the same order as the failed instances above. "
        "Include only the listed instances; instances that already compile are kept separately. "
        "Do not include explanations outside the code blocks."
    )


def repair_suite(checker, requirement, model, task, request, max_attempts=3, checkpoint=None):
    """Keep passing commands and request all remaining fixes in one call per round.

    State and costs are saved after every response. On resume, completed rounds
    count against the same attempt budget and their model calls are not repeated.
    """
    if "generation" not in requirement:
        requirement["generation"] = {
            key: requirement[key] for key in
            ("instances", "input tokens", "output tokens", "cached input tokens")
            if key in requirement
        }
    state = requirement.get("syntax repair")
    if state is None:
        entries = []
        for candidate in split_instances(requirement["instances"]):
            expectations = EXPECT.findall(mask_trivia(candidate))
            entries.append({"instances": candidate, "expect": int(expectations[-1]) if expectations else None})
        state = requirement["syntax repair"] = {"instances": entries, "rounds": []}
    entries = state["instances"]
    state["max attempts"] = max_attempts
    state["complete"] = False
    format_error = state.get("format error")

    while True:
        feedback = []
        for index, entry in enumerate(entries, start=1):
            error = checker.feedback(model, entry["instances"], entry["expect"])
            if error is not None:
                if format_error:
                    error += f"\nPrevious repair response format error: {format_error}"
                feedback.append({"instance": index, "error": error})
        state["errors"] = feedback
        if not feedback or len(state["rounds"]) >= max_attempts:
            state["complete"] = True
            state["successful"] = not feedback
            if checkpoint is not None:
                checkpoint()
            return
        if checkpoint is not None:
            checkpoint()

        response = request(repair_prompt(task, entries, feedback))
        replacements = replacement_instances(response.text)
        record = {
            "feedback": feedback, "response": response.text,
            "input tokens": response.input_tokens, "output tokens": response.output_tokens,
        }
        for field in ("input tokens", "output tokens", "cached input tokens"):
            if field in requirement:
                count = getattr(response, field.replace(" ", "_"))
                requirement[field] += count
                record[field] = count
        if len(replacements) == len(feedback):
            for issue, replacement in zip(feedback, replacements):
                entries[issue["instance"] - 1]["instances"] = replacement
            format_error = None
            state.pop("format error", None)
        else:
            format_error = (
                f"Expected {len(feedback)} separate repaired run command(s), "
                f"received {len(replacements)}. No replacements were applied."
            )
            state["format error"] = record["format error"] = format_error
        requirement["instances"] = "\n\n".join(entry["instances"] for entry in entries)
        record["instances"] = requirement["instances"]
        state["rounds"].append(record)
        if checkpoint is not None:
            checkpoint()
