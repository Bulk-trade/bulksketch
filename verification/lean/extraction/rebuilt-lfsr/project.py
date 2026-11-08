#!/usr/bin/env python3
"""Check the original rebuilt verifier and its scoped Rust std bindings."""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/rebuilt-lfsr")
RAW = DIRECTORY / "Arithmetic"
RUNTIME = Path("bridge/Arithmetic/RebuiltLfsrRuntime.lean")
ACTIVE_TYPES = Path("bridge/Arithmetic/RebuiltLfsrTypes.lean")
ACTIVE_FUNS = Path("bridge/Arithmetic/RebuiltLfsrGenerated.lean")
SHARED = ("bridge/Arithmetic/Types.lean", "bridge/Arithmetic/SliceKernelTypes.lean")
EXTERNALS = {
    "Mut1A.Insts.CoreCmpPartialEqShared0B.ne",
    "MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter",
    "core.slice.raw.from_ref",
} | {
    "core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice." + name
    for name in ("get", "get_mut", "get_unchecked", "get_unchecked_mut", "index", "index_mut")
}
NAMES = ["Slice.Insts.CoreCmpPartialEqSlice", *[
    "decode.verify.rebuilt_lfsr" + suffix
    for suffix in ("_loop0.body", "_loop0", "_loop1.body", "_loop1", "")
]]
HEADER = """-- Exact original source declarations with scoped standard-library bindings.
module
public import Arithmetic.RebuiltLfsrRuntime
public import Arithmetic.SliceKernelTypes
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

local notation "core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice" =>
  RebuiltLfsrRuntime.inclusive
local notation "Mut1A.Insts.CoreCmpPartialEqShared0B.ne" => RebuiltLfsrRuntime.mutableSharedNe
local notation "MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter" =>
  RebuiltLfsrRuntime.mutableIntoIter

"""


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parts(source):
    head, body = source.split("namespace bulksketch\n", 1)
    return head + "namespace bulksketch\n", re.findall(
        r"(?ms)^/--.*?(?=^/--|\Z)", body.rsplit("end bulksketch", 1)[0])


def check(root=ROOT, types=False):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    expected = {str(RAW / name) for name in ("Types.lean", "Funs.lean", "FunsExternal_Template.lean")}
    expected.update(str(DIRECTORY / name) for name in ("arithmetic.llbc", "charon.log", "aeneas.log"))
    if (receipt["status"] != "generated" or receipt["llbc_has_errors"] is not False or
            len(receipt["artifacts"]) != len(expected) or
            {entry["path"] for entry in receipt["artifacts"]} != expected):
        raise ValueError("incomplete rebuilt verifier extraction receipt")
    for entry in receipt["artifacts"]:
        if sha(root / entry["path"]) != entry["sha256"]:
            raise ValueError("raw rebuilt verifier extraction mismatch: " + entry["path"])
    if json.loads((root / DIRECTORY / "arithmetic.llbc").read_text())["has_errors"] is not False:
        raise ValueError("rebuilt verifier LLBC is incomplete")
    if sha(root / RUNTIME) != receipt["runtime_sha256"]:
        raise ValueError("scoped rebuilt verifier runtime mismatch")
    template = (root / RAW / "FunsExternal_Template.lean").read_text()
    external_names = re.findall(r"(?m)^axiom\s+(\S+)", template)
    if len(external_names) != len(EXTERNALS) or set(external_names) != EXTERNALS:
        raise ValueError("rebuilt verifier external declaration set changed")
    type_head, type_blocks = parts((root / RAW / "Types.lean").read_text())
    shared = "\n".join((root / path).read_text() for path in SHARED)
    if len(type_blocks) != 7 or any(block.strip() not in shared for block in type_blocks[1:]):
        raise ValueError("shared rebuilt verifier type mismatch")
    if (root / ACTIVE_TYPES).read_text() != type_head + "\n" + type_blocks[0] + "end bulksketch\n":
        raise ValueError("compiled rebuilt verifier inclusive range type differs")
    _, fun_blocks = parts((root / RAW / "Funs.lean").read_text())
    selected = []
    names = []
    for block in fun_blocks:
        declaration = re.search(r"(?m)^(?:def|impl_def)\s+(\S+)", block)
        if declaration and declaration.group(1) in NAMES:
            selected.append(block)
            names.append(declaration.group(1))
    if names != NAMES or (root / ACTIVE_FUNS).read_text() != HEADER + "".join(selected) + "end bulksketch\n":
        raise ValueError("compiled rebuilt verifier projection differs")
    raw, active, declarations = (
        (RAW / "Types.lean", ACTIVE_TYPES, ["core.ops.range.RangeToInclusive"]) if types else
        (RAW / "Funs.lean", ACTIVE_FUNS, names))
    return {
        "raw_generated_file": str(raw),
        "raw_file_sha256": sha(root / raw),
        "compiled_projection": str(active),
        "projection_file_sha256": sha(root / active),
        "source_declarations_retained_verbatim": len(declarations),
        "shared_types_and_function_dictionary_declarations_checked": True,
        "generated_declarations": ["bulksketch." + name for name in declarations],
        "native_source_edited": False,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--types", action="store_true")
    print(json.dumps(check(types=parser.parse_args().types), indent=2))
