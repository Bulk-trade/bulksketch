#!/usr/bin/env python3
"""Check original Dense square declarations and their scoped iterator bindings."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
EXTRACTION = "extraction/dense-square"
RUNTIME = "bridge/Arithmetic/DenseSquareRuntime.lean"
PREFIX = "poly.Dense.Insts.BulksketchPolyPolynomial.square_into"
FUNCTIONS = [PREFIX + suffix for suffix in ["_loop.body", "_loop", ""]]
BINDINGS = {
    "core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT": "leftNext",
    "core.iter.traits.iterator.Iterator.step_by.trait_default": "stepBy",
    "core.iter.traits.iterator.IteratorStepBy": "stepNext",
    "core.iter.traits.iterator.Iterator.zip.trait_default": "zip",
    "core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next": "next",
}
SHARED_TYPES = ["bridge/Arithmetic/Types.lean", "bridge/Arithmetic/SliceKernelTypes.lean",
                "bridge/Arithmetic/DenseNormalizationTypes.lean"]
NORMALIZATION = "bridge/Arithmetic/DenseNormalizationGenerated.lean"
ARTIFACTS = {f"{EXTRACTION}/{name}" for name in ["arithmetic.llbc", "charon.log", "aeneas.log",
    "Arithmetic/Funs.lean", "Arithmetic/Types.lean", "Arithmetic/FunsExternal_Template.lean"]}
HEADER = """-- Exact original source declarations. Local notation binds the scoped std runtime.
module
public import Arithmetic.DenseSquareRuntime
public import Arithmetic.DenseNormalizationGenerated
public import Arithmetic.SliceKernelTypes
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

""" + "".join(
    f'local notation "{source}" => Aeneas.Std.DenseSquareRuntime.{model}\n'
    for source, model in BINDINGS.items()
) + "\n"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def blocks(path):
    body = path.read_text().split("namespace bulksketch\n", 1)[1].rsplit("end bulksketch", 1)[0]
    return re.findall(r"(?ms)^/--.*?(?=^/--|\Z)", body)


def check(root=ROOT):
    receipt = json.loads((root / EXTRACTION / "receipt.json").read_text())
    if receipt["status"] != "generated" or receipt["llbc_has_errors"] is not False:
        raise ValueError("Dense square extraction is incomplete")
    if len(receipt["artifacts"]) != len(ARTIFACTS) or \
            {item["path"] for item in receipt["artifacts"]} != ARTIFACTS:
        raise ValueError("Dense square raw artifact set changed")
    for item in receipt["artifacts"]:
        if sha(root / item["path"]) != item["sha256"]:
            raise ValueError("raw Dense square extraction mismatch: " + item["path"])
    refinement = json.loads((root / EXTRACTION / "refinement-receipt.json").read_text())
    if sha(root / RUNTIME) != refinement["files_sha256"][RUNTIME]:
        raise ValueError("scoped Dense square runtime mismatch")
    shared_types = "\n".join((root / path).read_text() for path in SHARED_TYPES)
    for block in blocks(root / EXTRACTION / "Arithmetic/Types.lean"):
        if block.strip() not in shared_types:
            raise ValueError("shared Dense square type mismatch: " + block[:120])
    raw = root / EXTRACTION / "Arithmetic/Funs.lean"
    retained = []
    names = []
    normalization = (root / NORMALIZATION).read_text()
    normalization_count = 0
    for block in blocks(raw):
        declaration = re.search(r"^(?:def|impl_def)\s+(\S+)", block, re.MULTILINE)
        if not declaration:
            raise ValueError("unrecognized Dense square declaration")
        name = declaration.group(1)
        if name in FUNCTIONS:
            retained.append(block)
            names.append(name)
        elif name == "poly.dense.normalized_len" or name.startswith("poly.dense.normalized_len."):
            normalization_count += 1
            if block.strip() not in normalization:
                raise ValueError("shared normalization declaration mismatch: " + name)
    if names != FUNCTIONS or normalization_count != 7:
        raise ValueError("Dense square or normalization declaration set changed")
    compiled = root / "bridge/Arithmetic/DenseSquareGenerated.lean"
    if compiled.read_text() != HEADER + "".join(retained) + "end bulksketch\n":
        raise ValueError("compiled Dense square projection differs")
    return {"raw_generated_file": str(raw.relative_to(root)), "raw_file_sha256": sha(raw),
            "compiled_projection": str(compiled.relative_to(root)), "projection_file_sha256": sha(compiled),
            "source_declarations_retained_verbatim": len(retained),
            "shared_types_and_function_dictionary_declarations_checked": True,
            "shared_normalization_declarations_checked": normalization_count,
            "scoped_standard_library_bindings": BINDINGS,
            "scoped_runtime_file": RUNTIME, "scoped_runtime_sha256": sha(root / RUNTIME),
            "generated_declarations": ["bulksketch." + name for name in names],
            "native_source_edited": False}


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
