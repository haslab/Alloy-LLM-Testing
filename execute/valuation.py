"""Inspect Alloy declarations, validate JSON valuations, and render run commands."""

from dataclasses import dataclass
from collections import Counter
import json
import re


def _name(label):
    return str(label).removeprefix("this/")


def decode_response(response):
    """Accept a JSON object, optionally wrapped in a single Markdown code fence."""
    fenced = re.fullmatch(r"\s*```(?:json)?\s*\n(.*?)\n```\s*", response, re.DOTALL)
    source = fenced.group(1) if fenced else response

    def unique_keys(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"Duplicate JSON key: {key!r}.")
            result[key] = value
        return result

    def reject_constant(value):
        raise ValueError(f"{value} is not a valid JSON value.")

    return json.loads(source, object_pairs_hook=unique_keys, parse_constant=reject_constant)


@dataclass(frozen=True)
class Field:
    key: str
    owner: str
    rows: tuple
    ordering: bool = False
    expression: str | None = None
    declaration: str | None = None
    multiplicity: str | None = None

    @property
    def arity(self):
        return len(self.rows[0])


class ValuationError(ValueError):
    def __init__(self, errors):
        self.errors = errors
        super().__init__("\n".join(errors))


class ValuationModel:
    def __init__(self, model, scope, checker):
        if scope is not None and (type(scope) is not int or scope < 0):
            raise ValueError("The maximum scope must be a nonnegative integer or omitted.")
        if not isinstance(model, str):
            raise ValueError("The Alloy model must be a source string.")
        self.model, self.scope, self.checker = model, scope, checker
        try:
            world = checker.parse(None, model)
        except checker.error as exc:
            raise ValueError(f"The original Alloy model does not compile: {exc}") from exc
        self.signatures = {
            _name(sig.label): sig for sig in world.getAllReachableSigs()
            if not sig.builtin and (str(sig.label).startswith("this/") or sig.isPrivate is None)
        }
        self.roots = [name for name, sig in self.signatures.items()
                      if hasattr(sig, "parent") and str(sig.parent.label) == "univ"]
        for name, sig in self.signatures.items():
            parents = ([_name(sig.parent.label)] if hasattr(sig, "parent") and name not in self.roots
                       else [_name(parent.label) for parent in sig.parents] if hasattr(sig, "parents") else [])
            if any(parent not in self.signatures for parent in parents):
                raise ValueError(f"Unsupported signature bounds for {name}: JSON atom sets require visible user-declared parent signatures.")
        self.fields = {}
        for owner, sig in self.signatures.items():
            if sig.isVariable is not None:
                raise ValueError("JSON valuations currently support static Alloy signatures and fields.")
            prefix = owner.rsplit("/", 1)[0] + "/" if "/" in owner else ""
            for field in sig.getFields():
                if not str(sig.label).startswith("this/") and field.isPrivate is not None:
                    continue
                if field.isVariable is not None:
                    raise ValueError("JSON valuations currently support static Alloy signatures and fields.")
                key = f"{owner} <: {prefix}{field.label}"
                rows = tuple(tuple(_name(column.label) for column in row) for row in field.type().fold())
                expression = field.decl().expr
                while hasattr(expression, "sub") and str(expression.op.name()) == "NOOP":
                    expression = expression.sub
                multiplicity = {"ONEOF": "one", "LONEOF": "lone", "SOMEOF": "some"}.get(
                    str(expression.op.name()) if hasattr(expression, "op") else "")
                declaration = str(field.decl().expr).replace("this/", "")
                self.fields[key] = Field(key, owner, rows, declaration=declaration,
                                         multiplicity=multiplicity)
        for module in world.getAllReachableModules():
            if str(module.getModuleName()) != "util/ordering":
                continue
            for function in module.getAllFunc():
                if str(function.label).endswith("/next") and len(function.decls) == 0:
                    domain = function.returnDecl.left
                    while hasattr(domain, "sub"):
                        domain = domain.sub
                    owner = _name(domain.label)
                    key = f"{owner} <: next"
                    if key in self.fields:
                        raise ValueError(f"An ordering relation conflicts with a declared field: {key}")
                    self.fields[key] = Field(key, owner, ((owner, owner),), ordering=True,
                                             expression=f"{owner} <: {_name(function.label)}")
        names = " ".join([model, *self.signatures, *self.fields])
        self.reserved = set(re.findall(r"[A-Za-z_][A-Za-z0-9_]*", names))

    def inventory(self):
        return {
            "top-level signatures": self.roots,
            "signatures": list(self.signatures),
            "fields": {key: {"arity": field.arity, "column types": field.rows,
                             **({"declared range": field.declaration} if field.declaration else {})}
                       for key, field in self.fields.items()},
        }

    def response_schema(self, positives, negatives):
        """Build a draft-07 schema for native Ollama constrained decoding.

        Tuple-form ``items`` fixes each column's scalar type and tuple length.
        Semantic constraints, including references between arrays, remain in
        the existing validator and Alloy model-consistency check.
        """
        for count in (positives, negatives):
            if type(count) is not int or count < 0:
                raise ValueError("Schema instance counts must be nonnegative integers.")

        def object_schema(properties):
            return {"type": "object", "properties": properties,
                    "required": list(properties), "additionalProperties": False}

        signatures = {}
        for name in self.signatures:
            signatures[name] = {"type": "array", "items": {"type": "string", "minLength": 1}}
            if self.scope is not None and name in self.roots:
                signatures[name]["maxItems"] = self.scope
        fields = {}
        for key, field in self.fields.items():
            columns = []
            for index in range(field.arity):
                types = {row[index] for row in field.rows}
                choices = []
                if types - {"Int"}:
                    choices.append({"type": "string", **({} if "String" in types else {"minLength": 1})})
                if "Int" in types:
                    choices.append({"type": "integer"})
                columns.append(choices[0] if len(choices) == 1 else {"anyOf": choices})
            fields[key] = {"type": "array", "items": {
                "type": "array", "items": columns, "additionalItems": False,
                "minItems": field.arity, "maxItems": field.arity,
            }}
        valuation = object_schema({
            "explanation": {"type": "string", "minLength": 1},
            "signatures": object_schema(signatures), "fields": object_schema(fields),
        })
        schema = object_schema({
            kind: {"type": "array", "items": valuation, "minItems": count, "maxItems": count}
            for kind, count in (("positive", positives), ("negative", negatives))
        })
        return {"$schema": "http://json-schema.org/draft-07/schema#", **schema}

    def declaration_feedback(self, instance):
        """Explain simple field multiplicities using the model's own declarations.

        This also works on partially malformed instances so a missing signature
        key does not hide an independent field error until the next repair round.
        """
        if not isinstance(instance, dict):
            return []
        values, fields = instance.get("signatures"), instance.get("fields")
        if not isinstance(values, dict) or not isinstance(fields, dict):
            return []
        errors = []
        for key, field in self.fields.items():
            if field.arity != 2 or field.multiplicity is None:
                continue
            atoms, rows = values.get(field.owner), fields.get(key)
            if not isinstance(atoms, list) or not isinstance(rows, list):
                continue
            tuples = {tuple(row) for row in rows if isinstance(row, list) and len(row) == 2
                      and all(type(value) in (str, int) for value in row)}
            counts = Counter(row[0] for row in tuples)
            for atom in atoms:
                if not isinstance(atom, str):
                    continue
                count = counts[atom]
                invalid = ((field.multiplicity == "one" and count != 1)
                           or (field.multiplicity == "lone" and count > 1)
                           or (field.multiplicity == "some" and count == 0))
                if invalid:
                    expected = {"one": "exactly one", "lone": "at most one", "some": "at least one"}[field.multiplicity]
                    errors.append(
                        f"{key}: declaration range '{field.declaration}' requires {expected} target "
                        f"for atom {atom!r}; found {count} distinct tuples. "
                        "Both positive and negative instances must respect this declaration."
                    )
        return errors

    def check_consistency(self, instance, command):
        """Check only the supplied model and valuation, never requirement oracles."""
        errors = self.declaration_feedback(instance)
        if errors:
            raise ValuationError(errors)
        if not hasattr(self, "_consistency_options"):
            from edu.mit.csail.sdg.translator import A4Options, TranslateAlloyToKodkod
            from kodkod.engine.satlab import SATFactory

            self._consistency_options = A4Options()
            self._consistency_options.solver = SATFactory.get("sat4j")
            self._execute = TranslateAlloyToKodkod.execute_command
        try:
            world = self.checker.parse(None, self.model + "\n" + command)
            solution = self._execute(None, world.getAllReachableSigs(), world.getAllCommands()[-1],
                                     self._consistency_options)
        except self.checker.error as exc:
            raise ValuationError([f"Alloy could not check model consistency: {exc}"]) from exc
        if not solution.satisfiable():
            raise ValuationError([
                "The concrete valuation is unsatisfiable with the supplied Alloy model. "
                "Check the model's field bounds, multiplicities, signature facts, and explicit facts. "
                "No natural language requirement oracle was added to this check. "
                "A negative instance must also satisfy the supplied model; it should violate only "
                "the target natural language requirement."
            ])

    def validate(self, instance):
        errors = []
        if not isinstance(instance, dict):
            raise ValuationError(["Each instance must be an object."])
        if set(instance) != {"explanation", "signatures", "fields"}:
            errors.append("Each instance must have exactly explanation, signatures, and fields.")
        if not isinstance(instance.get("explanation"), str) or not instance["explanation"].strip():
            errors.append("explanation must be a nonempty string.")
        values, fields = instance.get("signatures"), instance.get("fields")
        for label, actual, expected in (("signatures", values, self.signatures), ("fields", fields, self.fields)):
            if not isinstance(actual, dict):
                errors.append(f"{label} must be an object.")
                continue
            missing, extra = set(expected) - set(actual), set(actual) - set(expected)
            if missing:
                errors.append(f"Missing {label}: {', '.join(sorted(missing))}.")
            if extra:
                errors.append(f"Unknown {label}: {', '.join(sorted(extra))}.")
        if errors:
            raise ValuationError(errors)

        for name, atoms in values.items():
            if not isinstance(atoms, list) or any(not isinstance(atom, str) or not atom for atom in atoms):
                errors.append(f"signatures[{name!r}] must be an array of nonempty atom identifiers.")
                continue
            if len(atoms) != len(set(atoms)):
                errors.append(f"signatures[{name!r}] contains repeated atoms.")
        if errors:
            raise ValuationError(errors)
        populations = {name: set(atoms) for name, atoms in values.items()}
        active = set()
        for name in self.roots:
            atoms = populations[name]
            if self.scope is not None and len(atoms) > self.scope:
                errors.append(f"{name} has {len(atoms)} atoms; maximum scope is {self.scope}.")
            if active & atoms:
                errors.append(f"Different top-level signatures share atom identifiers: {sorted(active & atoms)}.")
            active.update(atoms)
        children = {}
        for name, sig in self.signatures.items():
            atoms = populations[name]
            if not atoms <= active:
                errors.append(f"{name} refers to atoms absent from the top-level signatures: {sorted(atoms - active)}.")
            if sig.isOne is not None and len(atoms) != 1:
                errors.append(f"{name} must contain exactly one atom.")
            if sig.isLone is not None and len(atoms) > 1:
                errors.append(f"{name} must contain at most one atom.")
            if sig.isSome is not None and not atoms:
                errors.append(f"{name} must contain at least one atom.")
            if hasattr(sig, "parent") and name not in self.roots:
                parent = _name(sig.parent.label)
                if not atoms <= populations.get(parent, set()):
                    errors.append(f"{name} must be a subset of {parent}.")
                children.setdefault(parent, []).append(name)
            elif hasattr(sig, "parents"):
                parents = [_name(parent.label) for parent in sig.parents]
                allowed = set().union(*(populations.get(parent, set()) for parent in parents))
                if not atoms <= allowed:
                    errors.append(f"{name} must be a subset of {' + '.join(parents)}.")
        for parent, names in children.items():
            seen = set()
            for name in names:
                if seen & populations[name]:
                    errors.append(f"The extensions of {parent} must be disjoint.")
                seen.update(populations[name])
        for name, sig in self.signatures.items():
            if sig.isAbstract is not None:
                covered = set().union(*(populations[child] for child in children.get(name, [])))
                if populations[name] != covered:
                    errors.append(f"Abstract signature {name} must equal the union of its extensions.")

        def matches(value, column):
            if column == "Int":
                return type(value) is int
            if column == "String":
                return isinstance(value, str)
            return isinstance(value, str) and value in populations.get(column, set())

        for key, field in self.fields.items():
            tuples = fields[key]
            if not isinstance(tuples, list):
                errors.append(f"fields[{key!r}] must be an array of tuples; use [] for empty.")
                continue
            seen = set()
            for index, row in enumerate(tuples, 1):
                path = f"fields[{key!r}] tuple {index}"
                if not isinstance(row, list) or len(row) != field.arity:
                    errors.append(f"{path} must have exactly {field.arity} elements.")
                    continue
                if any(type(value) not in (str, int) for value in row):
                    errors.append(f"{path} must contain atom identifiers, integer values, or string values.")
                    continue
                serialized = json.dumps(row)
                if serialized in seen:
                    errors.append(f"{path} repeats an earlier tuple.")
                seen.add(serialized)
                if row[0] not in populations[field.owner]:
                    errors.append(f"{path} must start with an atom of {field.owner}.")
                if not any(all(matches(value, column) for value, column in zip(row, types)) for types in field.rows):
                    errors.append(f"{path} contains missing atoms or values of the wrong types; expected {field.rows}.")
            if field.ordering and all(isinstance(row, list) and len(row) == 2
                                      and all(isinstance(value, str) for value in row) for row in tuples):
                atoms = populations[field.owner]
                edges = [tuple(row) for row in tuples]
                sources, targets = [row[0] for row in edges], [row[1] for row in edges]
                valid = bool(atoms) and len(edges) == len(atoms) - 1 and len(set(sources)) == len(sources) and len(set(targets)) == len(targets)
                start = atoms - set(targets)
                visited = set()
                if valid and len(start) == 1:
                    next_atom = next(iter(start))
                    successors = dict(edges)
                    while next_atom not in visited:
                        visited.add(next_atom)
                        if next_atom not in successors:
                            break
                        next_atom = successors[next_atom]
                    valid = visited == atoms
                else:
                    valid = False
                if not valid:
                    errors.append(f"{key} must form one immediate-successor chain over its nonempty signature; a singleton has [].")
        if errors:
            raise ValuationError(errors)

    def render(self, instance, classification, index):
        self.validate(instance)
        values, fields = instance["signatures"], instance["fields"]
        variables, quantifiers, used_names = {}, [], set(self.reserved)
        counter = 0
        for root in self.roots:
            names = []
            for atom in values[root]:
                counter += 1
                name = f"jsonAtom{counter}"
                while name in used_names:
                    name += "_"
                used_names.add(name)
                variables[atom] = name
                names.append(name)
            if names:
                quantifiers.append(f"    some disj {', '.join(names)} : {root} |")
        assignments = [f"{name} = " + (" + ".join(variables[atom] for atom in atoms) if atoms else "none")
                       for name, atoms in values.items()]
        integers = []
        for key, tuples in fields.items():
            field, rendered = self.fields[key], []
            for row in tuples:
                types = next(types for types in field.rows if all(
                    (type(value) is int if column == "Int" else isinstance(value, str) if column == "String"
                     else isinstance(value, str) and value in values.get(column, []))
                    for value, column in zip(row, types)))
                terms = []
                for value, column in zip(row, types):
                    if column == "Int":
                        integers.append(value)
                        terms.append(str(value))
                    elif column == "String":
                        terms.append(json.dumps(value))
                    else:
                        terms.append(variables[value])
                rendered.append("->".join(terms))
            assignments.append(f"{field.expression or key} = " + (" + ".join(rendered) if rendered else "->".join(["none"] * field.arity)))
        bounds = [f"exactly {len(values[root])} {root}" for root in self.roots]
        if integers:
            bits = 4
            while min(integers) < -(2 ** (bits - 1)) or max(integers) >= 2 ** (bits - 1):
                bits += 1
            bounds.append(f"{bits} Int")
        overall = self.scope if self.scope is not None else max((len(values[root]) for root in self.roots), default=3)
        scope = f"for {overall}" + (" but " + ", ".join(bounds) if bounds else "")
        # JSON identifiers and explanations never become executable Alloy text.
        explanation = " ".join(instance["explanation"].split())
        lines = [f"// {explanation}", f"run {classification}{index} {{"]
        if quantifiers:
            lines += quantifiers + ["    {"] + [f"        {line}" for line in assignments] + ["    }"]
        else:
            lines += [f"    {line}" for line in assignments]
        lines.append(f"}} {scope} expect {1 if classification == 'positive' else 0}")
        command = "\n".join(lines)
        feedback = self.checker.feedback(self.model, command, 1 if classification == "positive" else 0)
        if feedback:
            raise ValuationError([f"Alloy compilation: {feedback}"])
        return command


def valuation_key(instance):
    """Detect repeated valuations even if their explanations or array order differ."""
    return json.dumps({section: {name: sorted(json.dumps(value) for value in values)
                                 for name, values in instance[section].items()}
                       for section in ("signatures", "fields")}, sort_keys=True)
