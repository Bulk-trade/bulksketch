#!/usr/bin/env python3
"""Check exact generated closure/wrapper declarations and shared dependencies."""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
HEADER = """-- Exact declaration projection from the reviewed original-source extraction.
-- Only imports/type sharing are adapted; declarations below remain verbatim.
module
public import Arithmetic.Types
public import Arithmetic.InverseGenerated
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

"""
POINTERS = ["P.Insts.CoreOpsFunction" + name for name in [
    "FnPairU64U64U64.call", "FnMutPairU64U64U64.call_mut", "FnOncePairU64U64U64.call_once",
    "FnOncePairU64U64U64", "FnMutPairU64U64U64", "FnPairU64U64U64",
    "FnTupleU64U64.call", "FnMutTupleU64U64.call_mut", "FnOnceTupleU64U64.call_once",
    "FnOnceTupleU64U64", "FnMutTupleU64U64", "FnTupleU64U64"]]
CLOSURE = "field.maps.inverse_using.closure.Insts.CoreOpsFunction"
FUNCTIONS = POINTERS + [CLOSURE + name for name in [
    "FnPairU64U32U64.call_loop.body", "FnPairU64U32U64.call_loop",
    "FnPairU64U32U64.call", "FnMutPairU64U32U64.call_mut", "FnOncePairU64U32U64.call_once",
    "FnOncePairU64U32U64", "FnMutPairU64U32U64", "FnPairU64U32U64"
]] + ["field.maps.inverse_using", "field.maps.inverse"]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(root=ROOT, types=False):
    receipt = json.loads((root / "extraction/inverse-wrappers/receipt.json").read_text())
    for item in receipt["generated"]:
        if sha(root / item["path"]) != item["sha256"]:
            raise ValueError("raw wrapper extraction drift: " + item["path"])
    raw_funs = root / "extraction/inverse-wrappers/Arithmetic/Funs.lean"
    raw_types = root / "extraction/inverse-wrappers/Arithmetic/Types.lean"
    compiled_funs = root / "bridge/Arithmetic/InverseUsingGenerated.lean"
    compiled_types = root / "bridge/Arithmetic/InverseUsingTypes.lean"
    body = raw_funs.read_text().split("namespace bulksketch\n", 1)[1].rsplit("end bulksketch", 1)[0]
    blocks = re.findall(r"(?ms)^/--.*?(?=^/--|\Z)", body)
    selected = []
    names = []
    shared = (root / "bridge/Arithmetic/Funs.lean").read_text()
    shared += (root / "bridge/Arithmetic/InverseGenerated.lean").read_text()
    for block in blocks:
        name = re.search(r"^def\s+(\S+)", block, re.MULTILINE)
        if name and name.group(1) in FUNCTIONS:
            selected.append(block)
            names.append(name.group(1))
        elif block.strip() not in shared:
            raise ValueError("shared wrapper function/dictionary mismatch: " + block[:120])
    if names != FUNCTIONS:
        raise ValueError("wrapper declaration set/order changed")
    expected = HEADER.replace("public import Arithmetic.Types", "public import Arithmetic.InverseUsingTypes")
    if compiled_funs.read_text() != expected + "".join(selected) + "end bulksketch\n":
        raise ValueError("compiled wrapper projection differs")
    body = raw_types.read_text().split("namespace bulksketch\n", 1)[1].rsplit("end bulksketch", 1)[0]
    aliases = []
    shared_types = (root / "bridge/Arithmetic/Types.lean").read_text()
    for block in re.findall(r"(?ms)^/--.*?(?=^/--|\Z)", body):
        if "def field.maps.inverse_using.closure " in block:
            aliases.append(block)
        elif block.strip() not in shared_types:
            raise ValueError("shared wrapper type mismatch")
    expected = HEADER.replace("public import Arithmetic.InverseGenerated\n", "")
    if len(aliases) != 1 or compiled_types.read_text() != expected + "".join(aliases) + "end bulksketch\n":
        raise ValueError("compiled wrapper type projection differs")
    raw, compiled = (raw_types, compiled_types) if types else (raw_funs, compiled_funs)
    return {"raw_generated_file": str(raw.relative_to(root)), "raw_file_sha256": sha(raw),
            "compiled_projection": str(compiled.relative_to(root)), "projection_file_sha256": sha(compiled),
            "source_declarations_retained_verbatim": 1 if types else len(FUNCTIONS),
            "shared_types_and_function_dictionary_declarations_checked": True,
            "generated_declarations": ["bulksketch.field.maps.inverse_using.closure"] if types else
                ["bulksketch." + name for name in FUNCTIONS],
            "adaptation": "Exact 22-function and one-type projections; shared original types, functions and dictionaries retained byte for byte. No replacement closure model.",
            "native_source_edited": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--types", action="store_true")
    print(json.dumps(check(types=parser.parse_args().types), indent=2))
