"""Use Z3 Optimize as AlloyMax's MaxSAT backend, retaining Alloy instance decoding."""

import fcntl
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile
import time

import jpype


def bridge_class():
    source = Path(__file__).resolve().parent / "java/edu/mit/csail/sdg/translator/Z3Bridge.java"
    translator = jpype.JClass("edu.mit.csail.sdg.translator.TranslateAlloyToKodkod")
    jar = Path(str(translator.class_.getProtectionDomain().getCodeSource().getLocation().toURI().getPath()))
    fingerprint = hashlib.sha256(source.read_bytes() + jar.read_bytes()).hexdigest()[:20]
    build = Path(tempfile.gettempdir()) / ("alloy-z3-bridge-" + fingerprint)
    build.mkdir(exist_ok=True)
    with (build / ".lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if not (build / "edu/mit/csail/sdg/translator/Z3Bridge.class").exists():
            try:
                result = subprocess.run(["javac", "--release", "17", "-cp", str(jar), "-d", str(build), str(source)],
                                        capture_output=True, text=True, check=True)
            except (OSError, subprocess.CalledProcessError) as exc:
                raise ValueError("Compiling the Z3 adapter requires a JDK: " + getattr(exc, "stderr", str(exc))) from exc
    jpype.addClassPath(str(build))
    return jpype.JClass("edu.mit.csail.sdg.translator.Z3Bridge")


def execute(world, options, output_prefix=None):
    try:
        import z3
    except ImportError as exc:
        raise ValueError("--solver z3 requires the z3-solver Python package") from exc
    from optimal import wcnf_to_smt2

    bridge = bridge_class()
    with tempfile.TemporaryDirectory(prefix="alloy-z3-") as directory:
        prefix = Path(output_prefix) if output_prefix is not None else Path(directory) / "problem"
        wcnf = prefix.with_suffix(".wcnf")
        smt2 = prefix.with_suffix(".smt2")

        def solve(path, variables):
            started = time.monotonic()
            wcnf_to_smt2(Path(str(path)), smt2)
            optimizer = z3.Optimize()
            optimizer.from_file(str(smt2))
            status = optimizer.check()
            if status == z3.unknown:
                raise ValueError("Z3 did not prove an optimum: " + optimizer.reason_unknown())
            if output_prefix is not None:
                prefix.with_suffix(".z3.json").write_text(json.dumps({
                    "backend": "z3", "version": z3.get_version_string(), "status": str(status),
                    "elapsed_seconds": time.monotonic() - started, "variables": int(variables),
                    "statistics": str(optimizer.statistics()),
                }, indent=2) + "\n")
            if status == z3.unsat:
                return None
            # Serialize once in native code, rather than crossing the Python/C
            # boundary for every CNF variable. Unassigned variables can be false.
            model = optimizer.model()
            serialized = model.sexpr()
            values = re.findall(r"\(define-fun d(\d+) \(\) Bool\s+(true|false)\)", serialized)
            declarations = [d for d in model.decls() if re.fullmatch(r"d\d+", str(d))]
            if len(values) != len(declarations):
                # Defensive fallback for a future Z3 pretty-printer change.
                truth = [int(str(d)[1:]) for d in declarations if z3.is_true(model[d])]
            else:
                truth = [int(variable) for variable, value in values if value == "true"]
            return jpype.JArray(jpype.JInt)(truth)

        callback = jpype.JProxy(bridge.Callback, dict(solve=solve))
        return bridge.execute(world.getAllReachableSigs(), world.getAllCommands()[0], options, callback, str(wcnf))
