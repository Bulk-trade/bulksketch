#!/usr/bin/env python3
"""Check an exact seven-declaration projection from the original Portable extraction.

The unmodified raw output is retained. All shared types and function declarations
must agree byte for byte with the active arithmetic extraction; only the module
import boundary is adapted. No opaque application or standard-library templates
are imported into the proof package.
"""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
PREFIX = "backend.portable.Portable.Insts.BulksketchBackendContractArithmetic."
METHODS = ["mul", "square", "frobenius", "trace", "solve_quadratic", "raw_mul", "reduce"]
HEADER = """-- Exact declaration projection from successful original-source Aeneas output.
-- All seven Portable method declarations below are retained verbatim.
-- Shared extracted types and function bodies are checked against Arithmetic.Funs.
module
public import Arithmetic.Funs
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace bulksketch

"""


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(root=ROOT):
    raw_path = root / "extraction/portable-forwarding/Portable/Funs.lean"
    active_path = root / "bridge/Arithmetic/PortableGenerated.lean"
    receipt = json.loads((root / "extraction/portable-forwarding/receipt.json").read_text())
    for item in receipt["generated"]:
        if sha(root / item["path"]) != item["sha256"]:
            raise ValueError("raw extraction mismatch: " + item["path"])
    raw = raw_path.read_text().split("namespace bulksketch\n", 1)[1].rsplit("end bulksketch", 1)[0]
    blocks = re.findall(r"(?ms)^/--.*?(?=^/--|\Z)", raw)
    selected = [block for block in blocks if re.search(r"^def\s+" + re.escape(PREFIX), block, re.MULTILINE)]
    names = [re.search(r"^def\s+(\S+)", block, re.MULTILINE).group(1) for block in selected]
    if names != [PREFIX + method for method in METHODS]:
        raise ValueError("selected Portable declaration set/order changed")
    if active_path.read_text() != HEADER + "".join(selected) + "end bulksketch\n":
        raise ValueError("compiled Portable projection differs")
    shared = (root / "bridge/Arithmetic/Funs.lean").read_text()
    for block in blocks:
        if block not in selected and block.strip() not in shared:
            raise ValueError("shared function/dictionary mismatch: " + block[:120])
    types = (root / "extraction/portable-forwarding/Portable/Types.lean").read_text()
    types = types.split("namespace bulksketch\n", 1)[1].rsplit("end bulksketch", 1)[0]
    shared_types = (root / "bridge/Arithmetic/Types.lean").read_text()
    for block in re.findall(r"(?ms)^/--.*?(?=^/--|\Z)", types):
        if block.strip() not in shared_types:
            raise ValueError("shared type mismatch: " + block[:120])
    declarations = "".join(selected)
    return {
        "raw_generated_file": str(raw_path.relative_to(root)), "raw_file_sha256": sha(raw_path),
        "compiled_projection": str(active_path.relative_to(root)), "projection_file_sha256": sha(active_path),
        "retained_declarations_sha256": hashlib.sha256(declarations.encode()).hexdigest(),
        "source_declarations_retained_verbatim": 7,
        "shared_types_and_function_dictionary_declarations_checked": True,
        "shared_functions_checked": len(blocks) - len(selected),
        "generated_declarations": ["bulksketch." + name for name in names],
        "adaptation": "Import Arithmetic.Funs; all seven Portable methods copied verbatim; every shared extracted type, function and Gf64 dictionary checked byte for byte.",
        "native_source_edited": False,
    }


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
