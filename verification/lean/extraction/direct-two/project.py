#!/usr/bin/env python3
"""Check the direct two-root extraction and its scoped iterator adapter."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/direct-two")
RAW = DIRECTORY / "Arithmetic"
ACTIVE = Path("bridge/Arithmetic/DirectTwoGenerated.lean")
RUNTIME = Path("bridge/Arithmetic/DirectTwoRuntime.lean")
OPTION_RUNTIME = Path("bridge/Arithmetic/ShapeWireRuntime.lean")
SHARED = ("bridge/Arithmetic/Types.lean", "bridge/Arithmetic/SliceKernelTypes.lean")
TYPE_NAMES = ["decode.direct.Pair", "decode.direct.two.closure"]
PREFIX = "decode.direct.two.closure.Insts.CoreOpsFunction"
FUN_NAMES = [PREFIX + suffix for suffix in (
    "FnMutTupleShared0U64Bool.call_mut", "FnOnceTupleShared0U64Bool.call_once",
    "FnOnceTupleShared0U64Bool", "FnMutTupleShared0U64Bool")] + ["decode.direct.two"]
EXTERNALS = {
    "core.iter.traits.iterator.Iterator.any.default",
    "core.option.Option.Insts.CoreOpsTry_traitTry.branch",
    "core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual",
    "core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any",
    "core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.any",
    "core.slice.raw.from_ref",
}
HEADER = """-- Exact original source declaration projection with scoped library bindings.
module
public import Arithmetic.SliceKernelTypes
public import Arithmetic.DirectTwoRuntime
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

local notation "core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any" =>
  DirectTwoRuntime.sharedAny

"""


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def blocks(path):
    body = path.read_text().split("namespace bulksketch\n", 1)[1].rsplit("end bulksketch", 1)[0]
    return re.findall(r"(?ms)^/--.*?(?=^/--|\Z)", body)


def declaration(block):
    name = re.search(r"(?m)^(?:def|structure|impl_def)\s+(\S+)", block)
    return name.group(1) if name else None


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    expected = {str(RAW / name) for name in ("Types.lean", "Funs.lean", "FunsExternal_Template.lean")}
    expected.update(str(DIRECTORY / name) for name in ("arithmetic.llbc", "charon.log", "aeneas.log"))
    artifacts = receipt["artifacts"]
    if (receipt["status"] != "generated" or receipt["llbc_has_errors"] is not False or
            len(artifacts) != len(expected) or {entry["path"] for entry in artifacts} != expected):
        raise ValueError("incomplete direct-two extraction receipt")
    for entry in artifacts:
        if sha(root / entry["path"]) != entry["sha256"]:
            raise ValueError("raw direct-two extraction mismatch: " + entry["path"])
    if json.loads((root / DIRECTORY / "arithmetic.llbc").read_text())["has_errors"] is not False:
        raise ValueError("direct-two LLBC is incomplete")
    if sha(root / RUNTIME) != receipt["runtime_sha256"] or \
            sha(root / OPTION_RUNTIME) != receipt["option_runtime_sha256"]:
        raise ValueError("scoped direct-two runtime mismatch")
    template = (root / RAW / "FunsExternal_Template.lean").read_text()
    external_names = re.findall(r"(?m)^axiom\s+(\S+)", template)
    if len(external_names) != len(EXTERNALS) or set(external_names) != EXTERNALS:
        raise ValueError("direct-two external declaration set changed")
    raw_types = blocks(root / RAW / "Types.lean")
    types = [block for block in raw_types if declaration(block) in TYPE_NAMES]
    shared = "\n".join((root / path).read_text() for path in SHARED)
    if (len(raw_types) != 8 or [declaration(block) for block in types] != TYPE_NAMES or
            any(block.strip() not in shared for block in raw_types if block not in types)):
        raise ValueError("shared direct-two type mismatch")
    raw = RAW / "Funs.lean"
    functions = [block for block in blocks(root / raw) if declaration(block) in FUN_NAMES]
    if ([declaration(block) for block in functions] != FUN_NAMES or
            (root / ACTIVE).read_text() != HEADER + "".join(types + functions) + "end bulksketch\n"):
        raise ValueError("compiled direct-two projection differs")
    return {"raw_generated_file": str(raw), "raw_file_sha256": sha(root / raw),
            "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
            "source_declarations_retained_verbatim": len(types) + len(functions),
            "shared_types_and_function_dictionary_declarations_checked": True,
            "generated_declarations": ["bulksketch." + name for name in TYPE_NAMES + FUN_NAMES],
            "native_source_edited": False}


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
