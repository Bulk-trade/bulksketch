#!/usr/bin/env python3
"""Check exact source bodies and the scoped mutable slice iterator bindings."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
EXTRACTION = "extraction/portable-xor"
RUNTIME = "bridge/Arithmetic/MutableZipRuntime.lean"
PREFIX = "backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels."
FUNCTIONS = [PREFIX + suffix for suffix in ["xor_assign_loop.body", "xor_assign_loop", "xor_assign"]]
STD_DICTIONARIES = [
    "core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair",
    "core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT",
]
HEADER = """-- Exact original XOR declarations. Only imports and scoped std bindings are adapted.
module
public import Arithmetic.Types
public import Arithmetic.MutableZipRuntime
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


def blocks(path):
    body = path.read_text().split("namespace bulksketch\n", 1)[1].rsplit("end bulksketch", 1)[0]
    return re.findall(r"(?ms)^/--.*?(?=^/--|\Z)", body)


def check(root=ROOT):
    receipt = json.loads((root / EXTRACTION / "receipt.json").read_text())
    for item in receipt["generated"]:
        if sha(root / item["path"]) != item["sha256"]:
            raise ValueError("raw XOR extraction mismatch: " + item["path"])
    if sha(root / RUNTIME) != receipt["scoped_runtime_sha256"]:
        raise ValueError("scoped mutable Zip runtime mismatch")
    raw_funs = root / EXTRACTION / "Arithmetic/Funs.lean"
    active = root / "bridge/Arithmetic/PortableXorGenerated.lean"
    retained = []
    names = []
    dictionaries = []
    for block in blocks(raw_funs):
        name = re.search(r"^(def|impl_def)\s+(\S+)", block, re.MULTILINE)
        if not name:
            raise ValueError("unrecognized raw XOR declaration")
        if name.group(1) == "def" and name.group(2) in FUNCTIONS:
            retained.append(block)
            names.append(name.group(2))
        elif name.group(1) == "impl_def" and name.group(2) in STD_DICTIONARIES:
            dictionaries.append(name.group(2))
        else:
            raise ValueError("unexpected raw XOR declaration: " + name.group(2))
    if names != FUNCTIONS or dictionaries != STD_DICTIONARIES:
        raise ValueError("XOR source or scoped std declaration set/order changed")
    if active.read_text() != HEADER + "".join(retained) + "end bulksketch\n":
        raise ValueError("compiled XOR projection differs")
    shared_types = (root / "bridge/Arithmetic/Types.lean").read_text()
    for block in blocks(root / EXTRACTION / "Arithmetic/Types.lean"):
        if block.strip() not in shared_types:
            raise ValueError("shared XOR type mismatch: " + block[:120])
    return {"raw_generated_file": str(raw_funs.relative_to(root)), "raw_file_sha256": sha(raw_funs),
            "compiled_projection": str(active.relative_to(root)), "projection_file_sha256": sha(active),
            "source_declarations_retained_verbatim": len(retained),
            "shared_types_and_function_dictionary_declarations_checked": True,
            "scoped_standard_library_dictionaries": dictionaries,
            "scoped_runtime_file": RUNTIME, "scoped_runtime_sha256": sha(root / RUNTIME),
            "generated_declarations": ["bulksketch." + name for name in names],
            "native_source_edited": False}


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
