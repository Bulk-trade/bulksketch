#!/usr/bin/env python3
"""Check the original AVX-512 register declarations and their scoped models."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
EXTRACTION = "extraction/avx512-register"
COMPILED = "bridge/Arithmetic/Avx512RegisterGenerated.lean"
RUNTIME = "bridge/Arithmetic/Avx512RegisterRuntime.lean"
PREFIX = "backend.x86_vpclmul512."
CLOSURE = PREFIX + "reduce_shift.closure"
FUNCTIONS = [PREFIX + suffix for suffix in ("raw",
    "reduce_shift.closure.Insts.CoreOpsFunctionFnTuple__m512i__m512i.call",
    "reduce_shift", "reduce_cl", "multiply")]
TYPES = ["types.RawProduct", "types.FieldId", "field.sealed.Sealed", "field.BinaryField", CLOSURE]
BINDINGS = {
    "core.core_arch.x86.__m512i": "Word512",
    "core.core_arch.x86.vpclmulqdq._mm512_clmulepi64_epi128": "clmul",
    "core.core_arch.x86.avx512f._mm512_slli_epi64": "shiftLeft",
    "core.core_arch.x86.avx512f._mm512_srli_epi64": "shiftRight",
    "core.core_arch.x86.avx512f._mm512_xor_si512": "xorWords",
    "core.core_arch.x86.avx512f._mm512_set1_epi64": "broadcast",
    "core.core_arch.x86.avx512f._mm512_unpacklo_epi64": "unpack false",
    "core.core_arch.x86.avx512f._mm512_unpackhi_epi64": "unpack true",
}
ARTIFACTS = {f"{EXTRACTION}/{name}" for name in
             ("arithmetic.llbc", "charon.log", "aeneas.log", "Arithmetic/Funs.lean",
              "Arithmetic/Types.lean", "Arithmetic/FunsExternal_Template.lean",
              "Arithmetic/TypesExternal_Template.lean")}
HEADER = """-- Exact original source declarations. Local notation binds the AVX-512 register model.
import Arithmetic.Avx512RegisterRuntime

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option linter.style.nameCheck false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace bulksketch

""" + "".join(
    f'local notation "{source}" => Aeneas.Std.Avx512Register.{model}\n'
    for source, model in BINDINGS.items()
) + "\n"


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
    functions = blocks(root / EXTRACTION / "Arithmetic/Funs.lean")
    retained = [name for name in functions if name.startswith(PREFIX)]
    if list(types) != TYPES or retained != FUNCTIONS:
        raise ValueError("AVX-512 raw declaration set changed")
    return HEADER + types[CLOSURE].rstrip() + "\n\n" + "".join(
        functions[name] for name in retained) + "end bulksketch\n"


def check(root=ROOT):
    receipt = json.loads((root / EXTRACTION / "receipt.json").read_text())
    if receipt["status"] != "generated" or receipt["llbc_has_errors"] is not False:
        raise ValueError("AVX-512 extraction is incomplete")
    if len(receipt["artifacts"]) != len(ARTIFACTS) or \
            {item["path"] for item in receipt["artifacts"]} != ARTIFACTS:
        raise ValueError("AVX-512 raw artifact set changed")
    for item in receipt["artifacts"]:
        if sha(root / item["path"]) != item["sha256"]:
            raise ValueError("AVX-512 raw artifact mismatch: " + item["path"])
    refinement = json.loads((root / EXTRACTION / "refinement-receipt.json").read_text())
    if sha(root / RUNTIME) != refinement["files_sha256"][RUNTIME]:
        raise ValueError("scoped AVX-512 runtime mismatch")
    if (root / COMPILED).read_text() != projection(root):
        raise ValueError("compiled AVX-512 projection differs")
    raw = EXTRACTION + "/Arithmetic/Funs.lean"
    return {"raw_generated_file": raw, "raw_file_sha256": sha(root / raw),
            "compiled_projection": COMPILED, "projection_file_sha256": sha(root / COMPILED),
            "source_declarations_retained_verbatim": len(FUNCTIONS),
            "source_type_declarations_retained_verbatim": 1,
            "shared_types_and_function_dictionary_declarations_checked": True,
            "scoped_standard_library_bindings": BINDINGS,
            "scoped_runtime_file": RUNTIME, "scoped_runtime_sha256": sha(root / RUNTIME),
            "generated_declarations": ["bulksketch." + name for name in FUNCTIONS]}


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
