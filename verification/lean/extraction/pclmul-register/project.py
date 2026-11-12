#!/usr/bin/env python3
"""Check the original PCLMUL wrapper and register-kernel projection."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/pclmul-register")
RAW = DIRECTORY / "Arithmetic"
RUNTIME = Path("bridge/Arithmetic/X86PclmulRuntime.lean")
ACTIVE = Path("bridge/Arithmetic/X86PclmulGenerated.lean")
EXTERNALS = {
    "core.core_arch.x86.__m128i", "core.array.iter.IntoIter",
    "core.core_arch.x86.pclmulqdq._mm_clmulepi64_si128",
    "core.core_arch.x86.sse2._mm_srli_si128", "core.core_arch.x86.sse2._mm_xor_si128",
    "core.core_arch.x86_64.sse2._mm_cvtsi64_si128", "core.core_arch.x86_64.sse2._mm_cvtsi128_si64",
    "Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter",
    "core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next",
    "core.num.I64.from_ne_bytes", "core.num.I64.to_ne_bytes",
    "core.num.U64.from_ne_bytes", "core.num.U64.to_ne_bytes",
}
NAMES = ["backend.x86_pclmul." + suffix for suffix in (
    "low", "words", "word", "reduced", "multiply",
    "Pclmul.Insts.BulksketchBackendContractArithmetic.mul",
    "Pclmul.Insts.BulksketchBackendContractArithmetic.square", "raw_product",
    "Pclmul.Insts.BulksketchBackendContractArithmetic.raw_mul")]
HEADER = """-- Exact original scalar x86 declarations with scoped x86 value bindings.
import Arithmetic.Funs
import Arithmetic.X86PclmulRuntime
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

local notation "core.core_arch.x86.__m128i" => X86PclmulRuntime.Xmm
local notation "core.core_arch.x86.pclmulqdq._mm_clmulepi64_si128" => X86PclmulRuntime.clmul
local notation "core.core_arch.x86.sse2._mm_srli_si128" => X86PclmulRuntime.shiftBytes
local notation "core.core_arch.x86.sse2._mm_xor_si128" => X86PclmulRuntime.xor
local notation "core.core_arch.x86_64.sse2._mm_cvtsi64_si128" => X86PclmulRuntime.moveIn
local notation "core.core_arch.x86_64.sse2._mm_cvtsi128_si64" => X86PclmulRuntime.moveOut
local notation "core.num.U64.to_ne_bytes" => X86PclmulRuntime.unsignedBytes
local notation "core.num.I64.to_ne_bytes" => X86PclmulRuntime.signedBytes
local notation "core.num.U64.from_ne_bytes" => X86PclmulRuntime.unsignedFromBytes
local notation "core.num.I64.from_ne_bytes" => X86PclmulRuntime.signedFromBytes

"""


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def blocks(path):
    body = path.read_text().split("namespace bulksketch\n", 1)[1].rsplit("end bulksketch", 1)[0]
    return re.findall(r"(?ms)^/--.*?(?=^/--|\Z)", body)


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    expected = {str(RAW / name) for name in
        ("Types.lean", "Funs.lean", "TypesExternal_Template.lean", "FunsExternal_Template.lean")}
    expected.update(str(DIRECTORY / name) for name in ("arithmetic.llbc", "charon.log", "aeneas.log"))
    artifacts = receipt["artifacts"]
    if (receipt["status"] != "generated" or receipt["llbc_has_errors"] is not False or
            receipt["target"] != "x86_64-apple-darwin" or
            len(artifacts) != len(expected) or {entry["path"] for entry in artifacts} != expected):
        raise ValueError("incomplete scalar x86 extraction receipt")
    for entry in artifacts:
        if sha(root / entry["path"]) != entry["sha256"]:
            raise ValueError("raw scalar x86 extraction mismatch: " + entry["path"])
    if json.loads((root / DIRECTORY / "arithmetic.llbc").read_text())["has_errors"] is not False:
        raise ValueError("scalar x86 LLBC is incomplete")
    if sha(root / RUNTIME) != receipt["runtime_sha256"]:
        raise ValueError("scoped scalar x86 runtime mismatch")
    external = "\n".join((root / RAW / path).read_text() for path in
                          ("TypesExternal_Template.lean", "FunsExternal_Template.lean"))
    declared = re.findall(r"(?m)^axiom\s+(\S+)", external)
    if len(declared) != len(EXTERNALS) or set(declared) != EXTERNALS:
        raise ValueError("scalar x86 external declaration set changed")
    shared_types = (root / "bridge/Arithmetic/Types.lean").read_text()
    types = blocks(root / RAW / "Types.lean")
    if len(types) != 4 or any(block.strip() not in shared_types for block in types):
        raise ValueError("shared scalar x86 type mismatch")
    shared_funs = (root / "bridge/Arithmetic/Funs.lean").read_text()
    raw = RAW / "Funs.lean"
    retained = []
    names = []
    shared_count = 0
    for block in blocks(root / raw):
        declaration = re.search(r"(?m)^def\s+(\S+)", block)
        if not declaration:
            raise ValueError("unexpected scalar x86 declaration")
        name = declaration.group(1)
        if name in NAMES:
            retained.append(block)
            names.append(name)
        elif name.startswith("field.gf64.reduce"):
            if block.strip() not in shared_funs:
                raise ValueError("shared scalar reduction declaration differs: " + name)
            shared_count += 1
        else:
            raise ValueError("unexpected scalar x86 declaration: " + name)
    if (names != NAMES or shared_count != 5 or
            (root / ACTIVE).read_text() != HEADER + "".join(retained) + "end bulksketch\n"):
        raise ValueError("compiled scalar x86 projection differs")
    return {"raw_generated_file": str(raw), "raw_file_sha256": sha(root / raw),
            "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
            "source_declarations_retained_verbatim": len(names),
            "shared_types_and_function_dictionary_declarations_checked": True,
            "generated_declarations": ["bulksketch." + name for name in names],
            "native_source_edited": False}


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
