#!/usr/bin/env python3
"""Check the exact record_bytes declaration and its scoped Try bindings."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[3]
EXTRACTION = "extraction/shape-admission/wire-size"
RUNTIME = "bridge/Arithmetic/ShapeWireRuntime.lean"
DECLARATION = "sketch.shape.record_bytes"
BINDINGS = [
    "core.option.Option.Insts.CoreOpsTry_traitTry.branch",
    "core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual",
    "core.result.Result.ok",
]
HEADER = """-- Exact original source declaration. Only imports and scoped std bindings are adapted.
module
public import Arithmetic.ShapeWireRuntime
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

"""


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def body(path):
    return path.read_text().split("namespace bulksketch\n", 1)[1].rsplit("end bulksketch", 1)[0]


def check(root=ROOT):
    receipt = json.loads((root / EXTRACTION / "receipt.json").read_text())
    expected = {EXTRACTION + "/Arithmetic/" + name for name in
                ("Funs.lean", "FunsExternal_Template.lean", "Types.lean")}
    generated = receipt["generated"]
    if (receipt["status"] != "generated" or receipt["llbc_has_errors"] is not False or
            len(generated) != len(expected) or {item["path"] for item in generated} != expected):
        raise ValueError("incomplete wire-size extraction receipt")
    llbc = root / EXTRACTION / "arithmetic.llbc"
    if sha(llbc) != receipt["llbc_sha256"] or json.loads(llbc.read_text())["has_errors"] is not False:
        raise ValueError("incomplete or stale wire-size LLBC")
    for item in generated:
        if sha(root / item["path"]) != item["sha256"]:
            raise ValueError("raw wire-size extraction mismatch: " + item["path"])
    if sha(root / RUNTIME) != receipt["scoped_runtime_sha256"]:
        raise ValueError("scoped wire-size runtime mismatch")
    if body(root / EXTRACTION / "Arithmetic/Types.lean").strip():
        raise ValueError("wire-size extraction unexpectedly declares types")
    templates = (root / EXTRACTION / "Arithmetic/FunsExternal_Template.lean").read_text()
    if re.findall(r"^axiom\s+(\S+)", templates, re.MULTILINE) != BINDINGS:
        raise ValueError("wire-size external declaration set changed")
    raw = root / EXTRACTION / "Arithmetic/Funs.lean"
    retained = body(raw).lstrip("\n")
    if re.findall(r"^def\s+(\S+)", retained, re.MULTILINE) != [DECLARATION]:
        raise ValueError("wire-size declaration set changed")
    compiled = root / "bridge/Arithmetic/ShapeWireGenerated.lean"
    if compiled.read_text() != HEADER + retained + "end bulksketch\n":
        raise ValueError("compiled wire-size projection differs")
    return {"raw_generated_file": str(raw.relative_to(root)), "raw_file_sha256": sha(raw),
            "compiled_projection": str(compiled.relative_to(root)), "projection_file_sha256": sha(compiled),
            "source_declarations_retained_verbatim": 1,
            "shared_types_and_function_dictionary_declarations_checked": True,
            "scoped_standard_library_bindings": BINDINGS,
            "scoped_runtime_file": RUNTIME, "scoped_runtime_sha256": sha(root / RUNTIME),
            "generated_declarations": ["bulksketch." + DECLARATION],
            "native_source_edited": False}


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
