#!/usr/bin/env python3
"""Check the original Dense coefficient body and shared source declarations."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
EXTRACTION = "extraction/dense-coefficient/xor-coefficient"
METHOD = "poly.Dense.Insts.BulksketchPolyPolynomial.xor_coefficient"
HEADER = """-- Exact original-source declaration projection. Imports are adapted only.
module
public import Arithmetic.SliceKernelTypes
public import Arithmetic.DenseNormalizationGenerated
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


def blocks(path):
    body = path.read_text().split("namespace bulksketch\n", 1)[1].rsplit("end bulksketch", 1)[0]
    return re.findall(r"(?ms)^/--.*?(?=^/--|\Z)", body)


def check(root=ROOT):
    receipt = json.loads((root / EXTRACTION / "receipt.json").read_text())
    for artifact in receipt["generated"]:
        if sha(root / artifact["path"]) != artifact["sha256"]:
            raise ValueError("raw Dense coefficient extraction mismatch: " + artifact["path"])
    raw_types = root / EXTRACTION / "Arithmetic/Types.lean"
    raw_funs = root / EXTRACTION / "Arithmetic/Funs.lean"
    compiled = root / "bridge/Arithmetic/DenseCoefficientGenerated.lean"
    type_modules = [
        (root / "bridge/Arithmetic" / name).read_text()
        for name in ("Types.lean", "SliceKernelTypes.lean", "DenseNormalizationTypes.lean")
    ]
    for block in blocks(raw_types):
        if not any(block.strip() in module for module in type_modules):
            raise ValueError("shared Dense coefficient type mismatch: " + block[:120])
    normalization = (root / "bridge/Arithmetic/DenseNormalizationGenerated.lean").read_text()
    method_blocks = []
    shared_count = 0
    for block in blocks(raw_funs):
        declaration = re.search(r"^def\s+(\S+)", block, re.MULTILINE)
        if declaration is None:
            continue
        name = declaration.group(1)
        if name == METHOD:
            method_blocks.append(block)
        elif name.startswith(("poly.dense.normalized_len", "core.slice.iter.Iter.Insts.CoreIterTraits")):
            if block.strip() not in normalization:
                raise ValueError("shared Dense normalization declaration mismatch: " + name)
            shared_count += 1
    if shared_count != 9:
        raise ValueError("Dense coefficient normalization declaration count differs")
    if len(method_blocks) != 1 or compiled.read_text() != HEADER + method_blocks[0] + "end bulksketch\n":
        raise ValueError("compiled Dense coefficient projection differs")
    return {"raw_generated_file": str(raw_funs.relative_to(root)), "raw_file_sha256": sha(raw_funs),
            "compiled_projection": str(compiled.relative_to(root)), "projection_file_sha256": sha(compiled),
            "source_declarations_retained_verbatim": 1,
            "shared_types_and_function_dictionary_declarations_checked": True,
            "shared_normalization_declarations": shared_count,
            "generated_declarations": ["bulksketch." + METHOD], "native_source_edited": False}


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
