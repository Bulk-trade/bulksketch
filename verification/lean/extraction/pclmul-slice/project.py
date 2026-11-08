#!/usr/bin/env python3
"""Verify exact accelerated PCLMUL slice declarations and reused models."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
EXTRACTION = "extraction/pclmul-slice"
COMPILED = "bridge/Arithmetic/X86PclmulSliceGenerated.lean"
BASE = "backend.x86_pclmul."
ENTRY = BASE + "Pclmul.Insts.BulksketchBackendContractArithmetic."
XOR = BASE + "Pclmul.Insts.BulksketchBackendContractBulkKernels.xor_assign"
SELECTED_ROOTS = [
    "{impl bulksketch::backend::contract::" + trait +
    " for bulksketch::backend::x86_pclmul::Pclmul}::" + name
    for trait, name in (("Arithmetic", "scale_xor"), ("Arithmetic", "square_slice"),
                        ("BulkKernels", "xor_assign"))
]
FUNCTIONS = [
    *(BASE + name for name in ("scale_xor_loop0.body", "scale_xor_loop0", "scale_xor_loop1.body",
        "scale_xor_loop1", "scale_xor")),
    ENTRY + "scale_xor",
    *(BASE + name for name in ("square_slice_loop.body", "square_slice_loop", "square_slice")),
    ENTRY + "square_slice", XOR + "_loop.body", XOR + "_loop", XOR,
]
SHARED = {
    "bridge/Arithmetic/Funs.lean": 5,
    "bridge/Arithmetic/X86PclmulGenerated.lean": 4,
    "extraction/affine-linear-eval/Arithmetic/Funs.lean": 2,
}
RUNTIMES = ["bridge/Arithmetic/X86PclmulRuntime.lean", "bridge/Arithmetic/MutableZipRuntime.lean"]
ARTIFACTS = {f"{EXTRACTION}/{name}" for name in
    ("arithmetic.llbc", "charon.log", "aeneas.log", "Arithmetic/Funs.lean",
     "Arithmetic/Types.lean", "Arithmetic/FunsExternal_Template.lean",
     "Arithmetic/TypesExternal_Template.lean")}
HEADER = """-- Exact original PCLMUL slice declarations and scoped XMM/Zip models.
import Arithmetic.X86PclmulGenerated
import Arithmetic.MutableZipRuntime

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace bulksketch

local notation "core.core_arch.x86.__m128i" => X86PclmulRuntime.Xmm
local notation "core.core_arch.x86.pclmulqdq._mm_clmulepi64_si128" => X86PclmulRuntime.clmul

"""


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def blocks(path):
    body = path.read_text().split("namespace bulksketch\n", 1)[1].rsplit("end bulksketch", 1)[0]
    result = {}
    for block in re.findall(r"(?ms)^/--.*?(?=^/--|\Z)", body):
        names = re.findall(r"(?m)^(?:def|impl_def|structure|inductive)\s+(\S+)", block)
        if len(names) != 1 or names[0] in result:
            raise ValueError("unrecognized or duplicate declaration in " + str(path))
        result[names[0]] = block
    return result


def projection(root):
    types = blocks(root / EXTRACTION / "Arithmetic/Types.lean")
    shared_types = blocks(root / "bridge/Arithmetic/Types.lean")
    if set(types) != {"types.FieldId", "field.sealed.Sealed", "field.BinaryField", "types.RawProduct"} or \
            any(block.rstrip() != shared_types[name].rstrip() for name, block in types.items()):
        raise ValueError("shared PCLMUL slice types differ")
    functions = blocks(root / EXTRACTION / "Arithmetic/Funs.lean")
    retained = [name for name in functions if name in FUNCTIONS]
    if retained != FUNCTIONS:
        raise ValueError("PCLMUL slice declarations changed")
    shared_files = {file: blocks(root / file) for file in SHARED}
    counts = dict.fromkeys(SHARED, 0)
    for name, block in functions.items():
        if name in FUNCTIONS:
            continue
        matches = [file for file, declarations in shared_files.items()
                   if name in declarations and block.rstrip() == declarations[name].rstrip()]
        if len(matches) != 1:
            raise ValueError("shared PCLMUL slice declaration differs or is ambiguous: " + name)
        counts[matches[0]] += 1
    if counts != SHARED:
        raise ValueError("shared PCLMUL slice declaration counts changed")
    return HEADER + "".join(functions[name] for name in FUNCTIONS) + "end bulksketch\n"


def check(root=ROOT):
    receipt = json.loads((root / EXTRACTION / "receipt.json").read_text())
    if receipt["status"] != "generated" or receipt["llbc_has_errors"] is not False:
        raise ValueError("PCLMUL slice extraction is incomplete")
    if len(receipt["artifacts"]) != len(ARTIFACTS) or \
            {item["path"] for item in receipt["artifacts"]} != ARTIFACTS:
        raise ValueError("PCLMUL slice raw artifact set changed")
    for item in receipt["artifacts"]:
        if sha(root / item["path"]) != item["sha256"]:
            raise ValueError("PCLMUL slice raw artifact mismatch: " + item["path"])
    llbc = json.loads((root / EXTRACTION / "arithmetic.llbc").read_text())
    if llbc["has_errors"] is not False or llbc["translated"]["options"]["start_from"] != SELECTED_ROOTS or \
            receipt["selected_roots"] != SELECTED_ROOTS or receipt["target"] != "x86_64-apple-darwin":
        raise ValueError("PCLMUL slice LLBC selection differs")
    for model in RUNTIMES:
        if sha(root / model) != receipt["runtime_files_sha256"][model]:
            raise ValueError("PCLMUL slice runtime differs: " + model)
    if (root / COMPILED).read_text() != projection(root):
        raise ValueError("compiled PCLMUL slice projection differs")
    raw = EXTRACTION + "/Arithmetic/Funs.lean"
    return {"raw_generated_file": raw, "raw_file_sha256": sha(root / raw),
            "compiled_projection": COMPILED, "projection_file_sha256": sha(root / COMPILED),
            "source_declarations_retained_verbatim": len(FUNCTIONS),
            "shared_types_and_function_dictionary_declarations_checked": True,
            "shared_declarations_checked": sum(SHARED.values()) + 4,
            "generated_declarations": ["bulksketch." + name for name in FUNCTIONS]}


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
