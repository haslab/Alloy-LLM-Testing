"""Explicit bounded declaration encodings for the four study examples.

Alloy resolves references before the source rewriter changes fields and ordering
functions. This is deliberately not a compiler for arbitrary Alloy declarations.
"""

from dataclasses import dataclass
from functools import lru_cache
import re


DEFAULT_SCOPE = 4


@dataclass(frozen=True)
class Relation:
    name: str
    columns: tuple
    output: str = ""


@dataclass(frozen=True)
class Benchmark:
    key: str
    index: int
    original: str
    domains: tuple  # (signature, atom-name prefix)
    signatures: tuple  # (signature, root domain)
    relations: tuple
    constraints: str
    aliases: tuple = ()  # ((declaring signature, field name), reified name)
    ordered: bool = False

    @property
    def names(self):
        return tuple(name for name, _ in self.signatures) + tuple(r.name for r in self.relations)

    def bitwidth(self, n, scope=DEFAULT_SCOPE):
        # Include relation cardinalities (Courses.grades can contain scope**3 tuples).
        bound = max(2 * n, scope ** max(len(r.columns) for r in self.relations))
        return max(5, bound.bit_length() + 1)

    @property
    def declarations(self):
        return self.render_declarations()

    def render_declarations(self, scope=DEFAULT_SCOPE):
        pools = ", ".join(d + "Atom" for d, _ in self.domains if not self.ordered or d != "Course")
        fields = ["valid : set Formula"]
        fields += [f"{name} : set {root}Atom" for name, root in self.signatures]
        roots = dict(self.signatures)
        stored = [r for r in self.relations if not self.ordered or r.name != "grades"]
        fields += [f"{r.name} : " + " -> ".join(roots[c] + "Atom" for c in r.columns)
                   for r in stored]
        bounds = [f"{r.name} in " + " -> ".join(r.columns) for r in stored]
        if self.ordered:
            # A four-column Instance->Course->Person->Grade field exceeds
            # Kodkod's tuple-index capacity once Formula has hundreds of atoms.
            fields += [f"grades{i} : PersonAtom -> GradeAtom" for i in range(1, scope + 1)]
            bounds += [f"grades{i} in Person -> Grade\n    CourseSlot{i} not in Course implies no grades{i}"
                       for i in range(1, scope + 1)]
        return (
            f"abstract sig Atom {{}}\nsig {pools} extends Atom {{}}\n"
            + ("abstract sig CourseAtom extends Atom {}\n"
               "one sig " + ", ".join(f"CourseSlot{i}" for i in range(1, scope + 1)) + " extends CourseAtom {}\n"
               "one sig OrderingAtom {}\n" if self.ordered else "")
            + "abstract sig Formula {}\none sig Oracle extends Formula {}\nsig detected in Formula {}\n"
            + "sig Instance {\n    " + ",\n    ".join(fields) + "\n} {\n    "
            + "\n    ".join(bounds) + "\n" + self.constraints + "\n"
        )

    @property
    def helpers(self):
        return self.render_helpers()

    def render_helpers(self, scope=DEFAULT_SCOPE):
        if not self.ordered:
            return ""
        grades = " + ".join(f"CourseSlot{i} -> i.grades{i}" for i in range(1, scope + 1))
        return ORDERING_HELPERS.replace("GRADES_TABLES", grades)


SOCIAL = Benchmark(
    "socialnetwork", 0,
    "sig User { follows : set User, sees : set Photo, posts : set Photo, suggested : set User } sig Influencer extends User {} sig Photo { date : one Day } sig Ad extends Photo {} sig Day {}",
    (("User", "u"), ("Photo", "p"), ("Day", "d")),
    (("User", "User"), ("Influencer", "User"), ("Photo", "Photo"), ("Ad", "Photo"), ("Day", "Day")),
    (Relation("follows", ("User", "User")), Relation("sees", ("User", "Photo")),
     Relation("posts", ("User", "Photo")), Relation("suggested", ("User", "User")),
     Relation("date", ("Photo", "Day"))),
    """    Influencer in User
    Ad in Photo
    date in Photo -> one Day""",
)

PRODUCTION = Benchmark(
    "productionline", 1,
    "sig Workstation { workers : set Worker, succ : set Workstation } one sig begin, end in Workstation {} sig Worker {} sig Human, Robot extends Worker {} abstract sig Product { parts : set Product } sig Material extends Product {} sig Component extends Product { workstation : set Workstation } sig Dangerous in Product {}",
    (("Workstation", "w"), ("Worker", "k"), ("Product", "p")),
    (("Workstation", "Workstation"), ("begin", "Workstation"), ("end", "Workstation"),
     ("Worker", "Worker"), ("Human", "Worker"), ("Robot", "Worker"),
     ("Product", "Product"), ("Material", "Product"), ("Component", "Product"), ("Dangerous", "Product")),
    (Relation("workers", ("Workstation", "Worker")), Relation("succ", ("Workstation", "Workstation")),
     Relation("parts", ("Product", "Product")), Relation("workstation", ("Component", "Workstation"))),
    """    one begin
    one end
    begin + end in Workstation
    Human + Robot in Worker
    no Human & Robot
    Product = Material + Component
    no Material & Component
    Dangerous in Product""",
)

TRAIN = Benchmark(
    "trainstation", 2,
    "sig Track { succs : set Track, signals : set Signal } sig Junction, Entry, Exit in Track {} sig Signal {} sig Semaphore, Speed extends Signal {}",
    (("Track", "t"), ("Signal", "s")),
    (("Track", "Track"), ("Junction", "Track"), ("Entry", "Track"), ("Exit", "Track"),
     ("Signal", "Signal"), ("Semaphore", "Signal"), ("Speed", "Signal")),
    (Relation("succs", ("Track", "Track")), Relation("signals", ("Track", "Signal"))),
    """    Junction + Entry + Exit in Track
    Semaphore + Speed in Signal
    no Semaphore & Speed""",
)

COURSES = Benchmark(
    "courses", 3,
    "open util/ordering[Grade] sig Person { teaches : set Course, enrolled : set Course, projects : set Project } sig Professor,Student in Person {} sig Course { projects : set Project, grades : Person -> Grade } sig Project {} sig Grade {}",
    (("Person", "p"), ("Course", "c"), ("Project", "j"), ("Grade", "g")),
    (("Person", "Person"), ("Professor", "Person"), ("Student", "Person"),
     ("Course", "Course"), ("Project", "Project"), ("Grade", "Grade")),
    (Relation("teaches", ("Person", "Course")), Relation("enrolled", ("Person", "Course")),
     Relation("personProjects", ("Person", "Project"), "Person <: projects"),
     Relation("courseProjects", ("Course", "Project"), "Course <: projects"),
     Relation("grades", ("Course", "Person", "Grade")),
     Relation("gradeNext", ("Grade", "Grade"), "Grade <: next")),
    """    Professor + Student in Person
    some Grade
    gradeNext in Grade -> lone Grade
    one Grade - Grade.gradeNext
    Grade = (Grade - Grade.gradeNext).*gradeNext
    no iden & ^gradeNext""",
    ((("Person", "projects"), "personProjects"), (("Course", "projects"), "courseProjects"),
     (("Course", "grades"), "(instanceGrades[this])")),
    ordered=True,
)

BENCHMARKS = {b.key: b for b in (SOCIAL, PRODUCTION, TRAIN, COURSES)}

# util/ordering's functions, applied to one Instance's Grade chain.
ORDERING_HELPERS = """
fun instanceGrades[i : Instance] : CourseAtom -> PersonAtom -> GradeAtom {
    GRADES_TABLES
}
fun order_first[i : Instance] : one GradeAtom { i.Grade - i.Grade.(i.gradeNext) }
fun order_last[i : Instance] : one GradeAtom { i.Grade - (i.gradeNext).(i.Grade) }
fun order_next[i : Instance] : GradeAtom -> GradeAtom { i.gradeNext }
fun order_prev[i : Instance] : GradeAtom -> GradeAtom { ~(i.gradeNext) }
fun order_prevs[i : Instance, e : GradeAtom] : set GradeAtom { e.^(~(i.gradeNext)) }
fun order_nexts[i : Instance, e : GradeAtom] : set GradeAtom { e.^(i.gradeNext) }
pred order_lt[i : Instance, a, b : GradeAtom] { b in a.^(i.gradeNext) }
pred order_gt[i : Instance, a, b : GradeAtom] { a in b.^(i.gradeNext) }
pred order_lte[i : Instance, a, b : GradeAtom] { a = b or order_lt[i, a, b] }
pred order_gte[i : Instance, a, b : GradeAtom] { a = b or order_gt[i, a, b] }
fun order_larger[i : Instance, a, b : GradeAtom] : GradeAtom { order_lt[i, a, b] => b else a }
fun order_smaller[i : Instance, a, b : GradeAtom] : GradeAtom { order_lt[i, a, b] => a else b }
fun order_max[i : Instance, es : set GradeAtom] : lone GradeAtom { es - es.^(~(i.gradeNext)) }
fun order_min[i : Instance, es : set GradeAtom] : lone GradeAtom { es - es.^(i.gradeNext) }
"""


@lru_cache(maxsize=8192)
def translate(expression, benchmark=SOCIAL):
    """Reify resolved field/order references while preserving the original syntax.

    Instance/Formula atoms and unused pool slots must not leak into univ or the
    identity added by reflexive closure. Keep the original local universe,
    including Int, String, and util/ordering's singleton implementation atom.
    """
    from edu.mit.csail.sdg.parser import CompUtil

    source = benchmark.original + "\nfact {\n" + expression + "\n}\n"
    start = len(benchmark.original) + len("\nfact {\n")
    world = CompUtil.parseEverything_fromString(None, source)
    root = world.getAllFacts().get(0).b
    singleton_variables = []

    def collect_singletons(node):
        kind = str(node.getClass().getSimpleName())
        if kind == "ExprQt":
            for decl in node.decls:
                if str(decl.expr.getClass().getSimpleName()) == "ExprUnary" and str(decl.expr.op.name()) == "ONEOF":
                    singleton_variables.extend(decl.names)
                collect_singletons(decl.expr)
        for name in ("sub", "left", "right", "cond", "expr"):
            if hasattr(node, name):
                collect_singletons(getattr(node, name))
        if hasattr(node, "args"):
            for arg in node.args:
                collect_singletons(arg)

    collect_singletons(root)
    offsets = [0]
    offsets += [i + 1 for i, char in enumerate(source) if char == "\n"]
    aliases = dict(benchmark.aliases)
    universe = "(" + " + ".join("this.@" + d for d, _ in benchmark.domains) + " + Int + String"
    if benchmark.ordered:
        universe += " + OrderingAtom"
    universe += ")"
    identity = f"({universe} <: iden)"

    def bounds(pos):
        return offsets[int(pos.y) - 1] + int(pos.x) - 1, offsets[int(pos.y2) - 1] + int(pos.x2)

    def expression_bounds(node):
        # Alloy spans omit some closing delimiters, e.g. the ')' in *(succ).
        lo, hi = bounds(node.span())
        stack = []
        missing_left = []
        for match in re.finditer(r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|[(){}\[\]]', source[lo:hi]):
            token = match.group()
            if token in ("(", "[", "{"):
                stack.append({"(": ")", "[": "]", "{": "}"}[token])
            elif stack and token == stack[-1]:
                stack.pop()
            elif token in (")", "]", "}"):
                missing_left.append({")": "(", "]": "[", "}": "{"}[token])
        for opening in missing_left:
            while lo and source[lo - 1].isspace():
                lo -= 1
            if source[lo - 1:lo] != opening:
                raise ValueError("Cannot recover leading Alloy expression delimiters")
            lo -= 1
        while stack:
            gap = re.match(r'(?:\s|//[^\n]*|/\*[\s\S]*?\*/)*', source[hi:]).end()
            hi += gap
            if source[hi:hi + 1] != stack.pop():
                raise ValueError("Cannot recover Alloy expression delimiters during reification")
            hi += 1
        return lo, hi

    def render(node):
        lo, hi = expression_bounds(node)
        return apply(lo, hi, edits(node))

    def apply(lo, hi, replacements):
        result = source[lo:hi]
        for a, b, value in sorted(set(replacements), reverse=True):
            if a < lo or b > hi:
                raise ValueError("Alloy source position outside expression during reification")
            result = result[:a - lo] + value + result[b - lo:]
        return result

    def replace(node, value, span=False):
        return [(*(expression_bounds(node) if span else bounds(node.pos())), value)]

    def unwrap(node):
        while str(node.getClass().getSimpleName()) == "ExprUnary" and str(node.op.name()) == "NOOP":
            node = node.sub
        return node

    def product_factors(node):
        original = node
        node = unwrap(node)
        kind = str(node.getClass().getSimpleName())
        if kind == "ExprBinary" and str(node.op.name()) == "ARROW":
            return product_factors(node.left) + product_factors(node.right)
        return [original]

    def edits(node):
        kind = str(node.getClass().getSimpleName())
        if kind == "ExprUnary":
            op = str(node.op.name())
            sub = node.sub
            if op in ("CARDINALITY", "NO", "SOME", "ONE", "LONE") and int(sub.type().arity()) > 3:
                factors = product_factors(sub)
                remaining = [f for f in factors if not any(unwrap(f).equals(v) for v in singleton_variables)]
                if len(remaining) < len(factors):
                    # Cartesian products with singleton-bound variables have
                    # exactly the same cardinality as the remaining factors.
                    # Avoid huge tuple spaces for s->c->projects / grades->c->s.
                    body = " -> ".join(f"({render(f)})" for f in remaining)
                    if not body:
                        value = "1" if op == "CARDINALITY" else "(no none)" if op != "NO" else "(some none)"
                    else:
                        operator = "#" if op == "CARDINALITY" else op.lower() + " "
                        value = f"({operator}({body}))"
                    return replace(node, value, span=True)
            if op == "NOOP":
                subkind = str(sub.getClass().getSimpleName())
                if subkind == "Field":
                    owner = str(sub.sig.label).split("/")[-1]
                    alias = aliases.get((owner, str(sub.label)))
                    return replace(node, alias) if alias else []
                if subkind == "PrimSig" and str(sub.label) == "univ":
                    return replace(node, universe)
                if subkind == "PrimSig" and str(sub.label) == "none":
                    # Alloy simplifies statically empty joins such as
                    # Project.projects to none, discarding their field nodes.
                    return replace(node, "->".join(["none"] * int(node.type().arity())), span=True)
            if op == "RCLOSURE":
                return replace(node, f"((^({render(sub)})) + {identity})", span=True)
            return edits(sub)
        if kind == "ExprConstant" and str(node.op.name()) == "IDEN":
            return replace(node, identity)
        if kind == "ExprCall":
            label = str(node.fun.label)
            if label.startswith("ordering/"):
                name = label.split("/")[-1]
                args = ", ".join(["this"] + [render(arg) for arg in node.args])
                return replace(node, f"(order_{name}[{args}])", span=True)
            return [edit for arg in node.args for edit in edits(arg)]
        if kind == "ExprBinary":
            return edits(node.left) + edits(node.right)
        if kind == "ExprList":
            return [edit for arg in node.args for edit in edits(arg)]
        if kind == "ExprQt":
            return [edit for d in node.decls for edit in edits(d.expr)] + edits(node.sub)
        if kind == "ExprLet":
            return edits(node.expr) + edits(node.sub)
        if kind == "ExprITE":
            return edits(node.cond) + edits(node.left) + edits(node.right)
        return []

    return apply(start, start + len(expression), edits(root))
