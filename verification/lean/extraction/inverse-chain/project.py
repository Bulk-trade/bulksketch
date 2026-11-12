#!/usr/bin/env python3
"""Check an exact declaration projection from the original inverse extraction.

The source-generated files are never edited. Only their import/type-sharing
boundary is adapted: common extracted declarations are reused from Arithmetic,
and all three inverse declarations are copied verbatim. This check fails if the
source extraction, shared types/dictionaries, or compiled projection changes.
"""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(root=ROOT):
    raw_path = root / "extraction/inverse-chain/Inverse/Funs.lean"
    types_path = root / "extraction/inverse-chain/Inverse/Types.lean"
    active_path = root / "bridge/Arithmetic/InverseGenerated.lean"
    receipt = json.loads((root / "extraction/inverse-chain/receipt.json").read_text())
    for item in receipt["generated"]:
        if sha(root / item["path"]) != item["sha256"]:
            raise ValueError(item["path"])
    raw = raw_path.read_text()
    start = raw.index("/-- [bulksketch::field::maps::inverse_with_frobenius]: loop body 0:")
    end = raw.index("/-- [bulksketch::field::{impl core::clone::Clone", start)
    declarations = raw[start:end]
    projected = active_path.read_text()
    if projected != HEADER + declarations + "end bulksketch\n":
        raise ValueError("compiled inverse projection differs")
    shared_types = types_path.read_text().split("namespace bulksketch\n\n", 1)[1].rsplit("end bulksketch", 1)[0]
    if shared_types not in (root / "bridge/Arithmetic/Types.lean").read_text():
        raise ValueError("shared type mismatch")
    shared_functions = raw[end:].rsplit("end bulksketch", 1)[0]
    # The dictionaries are byte-identical even though their order differs in
    # the larger arithmetic extraction. Check each complete declaration block.
    active_functions = (root / "bridge/Arithmetic/Funs.lean").read_text()
    for block in shared_functions.split("\n/-- "):
        block = block.strip()
        if not block:
            continue
        if not block.startswith("/-- "):
            block = "/-- " + block
        if block not in active_functions:
            raise ValueError("shared dictionary/function mismatch: " + block[:120])
    return {
        "raw_generated_file": str(raw_path.relative_to(root)), "raw_file_sha256": sha(raw_path),
        "compiled_projection": str(active_path.relative_to(root)), "projection_file_sha256": sha(active_path),
        "retained_declarations_sha256": hashlib.sha256(declarations.encode()).hexdigest(),
        "source_declarations_retained_verbatim": 3,
        "shared_types_and_function_dictionary_declarations_checked": True,
        "adaptation": "Import Arithmetic.Funs; shared extracted types and Gf64 dictionaries checked verbatim; all three inverse declarations retained byte-identically.",
        "native_source_edited": False,
    }


HEADER = """-- Exact declaration projection from the successful original-source Aeneas output.
-- Original output remains unchanged under extraction/inverse-chain/Inverse/.
-- Only the import/type reuse boundary is adapted; all three source declaration
-- texts below are byte-identical to that output. Existing Gf64 declarations are
-- reused from Arithmetic.Funs to avoid duplicate global declarations.
module
public import Arithmetic.Funs
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

"""

if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
