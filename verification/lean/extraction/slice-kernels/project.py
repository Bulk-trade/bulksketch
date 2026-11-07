#!/usr/bin/env python3
"""Check the original descending-update bodies and their generated dictionaries."""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
EXTRACTION = "extraction/slice-kernels/multiply-linear"
HEADER = """-- Exact original-source declaration projection. Imports are adapted only.
module
public import Arithmetic.Types
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

"""
TYPES = ["backend.contract.Arithmetic", "backend.contract.BulkKernels"]
FUNCTIONS = ["backend.contract.BulkKernels." + name for name in [
    "square_mod.default", "multiply_linear.default_loop.body",
    "multiply_linear.default_loop", "multiply_linear.default"]]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def blocks(path):
    body = path.read_text().split("namespace bulksketch\n", 1)[1].rsplit("end bulksketch", 1)[0]
    return re.findall(r"(?ms)^/--.*?(?=^/--|\Z)", body)


def check(root=ROOT, types=False):
    receipt = json.loads((root / EXTRACTION / "receipt.json").read_text())
    for artifact in receipt["generated"]:
        if sha(root / artifact["path"]) != artifact["sha256"]:
            raise ValueError("raw slice extraction mismatch: " + artifact["path"])
    raw_types = root / EXTRACTION / "Arithmetic/Types.lean"
    raw_funs = root / EXTRACTION / "Arithmetic/Funs.lean"
    compiled_types = root / "bridge/Arithmetic/SliceKernelTypes.lean"
    compiled_funs = root / "bridge/Arithmetic/SliceKernelGenerated.lean"
    shared_types = (root / "bridge/Arithmetic/Types.lean").read_text()
    type_blocks = []
    type_names = []
    for block in blocks(raw_types):
        name = re.search(r"^structure\s+(\S+)", block, re.MULTILINE)
        if name and name.group(1) in TYPES:
            type_blocks.append(block)
            type_names.append(name.group(1))
        elif block.strip() not in shared_types:
            raise ValueError("shared slice type mismatch: " + block[:120])
    if type_names != TYPES or compiled_types.read_text() != HEADER + "".join(type_blocks) + "end bulksketch\n":
        raise ValueError("compiled slice type projection differs")
    fun_blocks = []
    names = []
    for block in blocks(raw_funs):
        name = re.search(r"^def\s+(\S+)", block, re.MULTILINE)
        if name and name.group(1) in FUNCTIONS:
            fun_blocks.append(block)
            names.append(name.group(1))
    expected = HEADER.replace("Arithmetic.Types", "Arithmetic.SliceKernelTypes")
    if names != FUNCTIONS or compiled_funs.read_text() != expected + "".join(fun_blocks) + "end bulksketch\n":
        raise ValueError("compiled slice body projection differs")
    raw, compiled, retained = (raw_types, compiled_types, type_names) if types else (raw_funs, compiled_funs, names)
    return {"raw_generated_file": str(raw.relative_to(root)), "raw_file_sha256": sha(raw),
            "compiled_projection": str(compiled.relative_to(root)), "projection_file_sha256": sha(compiled),
            "source_declarations_retained_verbatim": len(retained),
            "shared_types_and_function_dictionary_declarations_checked": True,
            "generated_declarations": ["bulksketch." + name for name in retained],
            "native_source_edited": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--types", action="store_true")
    print(json.dumps(check(types=parser.parse_args().types), indent=2))
