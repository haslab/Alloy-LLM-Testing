"""Check uniqueness of static Alloy test instances modulo atom renaming."""


def kind(expression):
    return str(expression.getClass().getSimpleName())


def unwrap(expression):
    while kind(expression) == "ExprUnary" and str(expression.op.name()) == "NOOP":
        expression = expression.sub
    return expression


def label(name):
    return str(name).removeprefix("this/")


class DefinitionChecker:
    def __init__(self, world):
        self.required = {}
        self.owners = {}
        self.orderings = {}
        self.predicates = []
        self.roots = set()
        for signature in world.getAllReachableSigs():
            if signature.builtin or not (str(signature.label).startswith("this/") or signature.isPrivate is None):
                continue
            name = str(signature.label)
            if hasattr(signature, "parent") and str(signature.parent.label) == "univ":
                self.roots.add(name)
            self.required[("sig", name)] = label(name)
            for field in signature.getFields():
                if not str(signature.label).startswith("this/") and field.isPrivate is not None:
                    continue
                key = ("field", name, str(field.label))
                self.required[key] = f"{label(name)} <: {field.label}"
                self.owners[key] = name
        for module in world.getAllReachableModules():
            for function in module.getAllFunc():
                if function.isPred:
                    self.predicates.append(function)
                if (str(module.getModuleName()) == "util/ordering"
                        and str(function.label).endswith("/next") and len(function.decls) == 0):
                    owner = str(unwrap(function.returnDecl.left).label)
                    key = ("ordering", str(function.label))
                    self.required[key] = f"{label(owner)} <: {function.label}"
                    self.owners[key] = owner
                    self.orderings[str(function.label)] = key

    def symbol(self, expression, aliases, resolving=frozenset()):
        expression = unwrap(expression)
        tag = kind(expression)
        if tag == "ExprVar" and str(expression.label) in aliases:
            name = str(expression.label)
            if name in resolving:
                return None
            return self.symbol(aliases[name], aliases, resolving | {name})
        if tag in ("PrimSig", "SubsetSig"):
            return ("sig", str(expression.label))
        if tag == "Field":
            return ("field", str(expression.sig.label), str(expression.label))
        if tag == "ExprCall" and not expression.args:
            return self.orderings.get(str(expression.fun.label))
        if tag == "ExprBinary" and str(expression.op.name()) == "DOMAIN":
            target = self.symbol(expression.right, aliases)
            domain = self.symbol(expression.left, aliases)
            if target in self.owners and domain == ("sig", self.owners[target]):
                return target
        return None

    def missing(self, command):
        """Recognize a sufficient concrete encoding for the uniqueness fast path."""
        issues = []
        groups = []

        def concrete(expression, atoms):
            expression = unwrap(expression)
            tag = kind(expression)
            if tag == "ExprVar":
                return expression in atoms
            if tag == "PrimSig":
                return str(expression.label) == "none"
            if tag == "ExprBinary" and str(expression.op.name()) in ("PLUS", "ARROW"):
                return concrete(expression.left, atoms) and concrete(expression.right, atoms)
            return False

        def visit(expression, aliases, calls, minimum_line=None, atoms=frozenset()):
            # command.formula includes model facts. They do not count as
            # valuations explicitly supplied by this test command.
            if minimum_line is not None:
                position = expression.pos()
                if str(position.filename) and str(position.filename) != str(command.pos().filename):
                    return set()
                line = int(position.y)
                if 0 < line < minimum_line:
                    return set()
            expression = unwrap(expression)
            tag = kind(expression)
            if tag == "ExprList" and str(expression.op.name()) == "AND":
                found = set()
                for argument in expression.args:
                    found.update(visit(argument, aliases, calls, minimum_line, atoms))
                return found
            if tag == "ExprBinary":
                operation = str(expression.op.name())
                if operation == "AND":
                    return (visit(expression.left, aliases, calls, minimum_line, atoms)
                            | visit(expression.right, aliases, calls, minimum_line, atoms))
                if operation == "EQUALS":
                    return {key for side, value in ((expression.left, expression.right),
                                                   (expression.right, expression.left))
                            if (key := self.symbol(side, aliases)) in self.required and concrete(value, atoms)}
            if tag == "ExprQt":
                if str(expression.op.name()) != "SOME":
                    issues.append("Atom quantifiers must use some over a top-level signature")
                    return set()
                bound = dict(aliases)
                quantified = set(atoms)
                for declaration in expression.decls:
                    domain = unwrap(declaration.expr)
                    if kind(domain) == "ExprUnary" and str(domain.op.name()) == "ONEOF":
                        domain = unwrap(domain.sub)
                    else:
                        issues.append("Quantified variables must each denote one atom")
                        continue
                    if kind(domain) != "PrimSig" or ("sig", str(domain.label)) not in self.required:
                        issues.append("Atoms must be quantified over top-level signatures")
                        continue
                    name = str(domain.label)
                    # Distinct branches of an extends hierarchy cannot share
                    # atoms. Ancestor/descendant domains can, so their separate
                    # atom groups still require the semantic uniqueness query.
                    if any(domain.intersects(other) for other in groups):
                        issues.append(f"Bind all {label(name)} atoms in one declaration")
                    groups.append(domain)
                    if len(declaration.names) > 1 and declaration.disjoint is None:
                        issues.append(f"Use disj for multiple atoms of {label(name)}")
                    for variable in declaration.names:
                        bound.pop(str(variable.label), None)
                        quantified.add(variable)
                return visit(expression.sub, bound, calls, minimum_line, frozenset(quantified))
            if tag == "ExprLet":
                bound = {**aliases, str(expression.var.label): expression.expr}
                return visit(expression.sub, bound, calls, minimum_line, atoms)
            if tag == "ExprCall" and expression.fun.isPred:
                name = str(expression.fun.label)
                if name not in calls:
                    return visit(expression.fun.getBody(), {}, calls | {name})
            return set()

        original = unwrap(command.nameExpr)
        # A named predicate command is expanded by Alloy into the predicate
        # body, whose source position precedes the run command.
        if kind(original) == "ExprVar":
            name = str(original.label)
            matches = [p for p in self.predicates
                       if str(p.label) in (name, "this/" + name) and len(p.decls) == 0]
            found = visit(matches[0].getBody(), {}, {str(matches[0].label)}) if len(matches) == 1 else set()
        else:
            found = visit(command.formula, {}, set(), int(command.pos().y))
        missing = [name for key, name in self.required.items() if key not in found]
        return missing + list(dict.fromkeys(issues))

    def witness_predicate(self, world, solution):
        """Encode the whole visible instance, allowing all renamings of its atoms."""
        from edu.mit.csail.sdg.parser import CompUtil

        def tuples(value):
            return [tuple(str(row.atom(i)) for i in range(row.arity())) for row in value]

        signatures = {str(sig.label): sig for sig in world.getAllReachableSigs()}
        reserved = {piece for key in self.required for name in key[1:] for piece in name.split("/")}
        variables, quantifiers = {}, []
        for name in sorted(self.roots):
            names = []
            for (atom,) in tuples(solution.eval(signatures[name])):
                variable = f"uniquenessAtom{len(variables) + 1}"
                while variable in reserved:
                    variable += "_"
                reserved.add(variable)
                variables[atom] = variable
                names.append(variable)
            if names:
                quantifiers.append(f"some disj {', '.join(names)} : {name} |")
        literals = {}
        for name in ("Int", "String"):
            if name in signatures:
                for (atom,) in tuples(solution.eval(signatures[name])):
                    literals[atom] = f"({atom})" if name == "Int" else atom

        assignments = []
        for key, display in self.required.items():
            if key[0] == "sig":
                value = tuples(solution.eval(signatures[key[1]]))
                arity = 1
            elif key[0] == "field":
                field = next(f for f in signatures[key[1]].getFields() if str(f.label) == key[2])
                value = tuples(solution.eval(field))
                arity = int(field.type().arity())
            else:
                expression = CompUtil.parseOneExpression_fromString(world, display)
                value = tuples(solution.eval(expression))
                arity = 2
            rows = []
            for row in value:
                terms = []
                for atom in row:
                    if atom not in variables and atom not in literals:
                        raise ValueError(f"Cannot encode instance atom {atom!r} for uniqueness checking.")
                    terms.append(variables[atom] if atom in variables else literals[atom])
                rows.append("->".join(terms))
            rhs = " + ".join(rows) or "->".join(["none"] * arity)
            assignments.append(f"{display} = {rhs}")
        return "{ " + " ".join(quantifiers) + " {\n" + "\n".join(assignments) + "\n} }"

    def unique(self, world, command, solution, options):
        """Rule out a satisfying structure outside the first witness's isomorphism class."""
        from edu.mit.csail.sdg.parser import CompUtil
        from edu.mit.csail.sdg.translator import TranslateAlloyToKodkod

        for signature in world.getAllReachableSigs():
            if signature.isVariable is not None or any(f.isVariable is not None for f in signature.getFields()):
                raise ValueError("Instance uniqueness checking currently supports static signatures and fields.")
        # Complete literal valuations of a disjoint atom pool already certify
        # uniqueness. Other encodings need the semantic query below.
        if not self.missing(command):
            return True
        predicate = self.witness_predicate(world, solution)
        outside = CompUtil.parseOneExpression_fromString(world, f"not ({predicate})")
        probe = command.change(command.formula.and_(outside))
        alternative = TranslateAlloyToKodkod.execute_command(
            None, world.getAllReachableSigs(), probe, options)
        return not alternative.satisfiable()
