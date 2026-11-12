#!/usr/bin/env python3
"""Check the original Portable Horner declarations and scoped bindings."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
EXTRACTION = "extraction/portable-horner"
COMPILED = "bridge/Arithmetic/PortableHornerGenerated.lean"
RUNTIME = "bridge/Arithmetic/PortableHornerRuntime.lean"
CLOSURE = "backend.portable.BulkKernelsPortableF.horner_many.closure"
PREFIX = "backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.horner_many"
FN_ONCE = CLOSURE + ".Insts.CoreOpsFunctionFnOncePairU64Shared0U64U64"
FN_MUT = CLOSURE + ".Insts.CoreOpsFunctionFnMutPairU64Shared0U64U64"
FUNCTIONS = [FN_MUT + ".call_mut", FN_ONCE + ".call_once", FN_ONCE, FN_MUT,
             PREFIX + "_loop.body", PREFIX + "_loop", PREFIX]
TYPES = ["types.FieldId", "field.sealed.Sealed", "field.BinaryField", "types.RawProduct", CLOSURE]
CORE = ["field.gf64." + suffix for suffix in
        ("reduce_loop0_loop0.body", "reduce_loop0_loop0", "reduce_loop0.body", "reduce_loop0",
         "reduce", "raw_mul_loop0.body", "raw_mul_loop0", "raw_mul_loop1.body", "raw_mul_loop1",
         "raw_mul", "mul")]
ZIP = "core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair"
DOUBLE_ENDED = "core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT"
ITER_MUT = "core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT"
MUL = "backend.portable.Portable.Insts.BulksketchBackendContractArithmetic.mul"
SHARED = {
    ZIP: "extraction/portable-xor/Arithmetic/Funs.lean",
    DOUBLE_ENDED: "bridge/Arithmetic/DenseNormalizationGenerated.lean",
    ITER_MUT: "extraction/portable-xor/Arithmetic/Funs.lean",
    **dict.fromkeys(CORE, "bridge/Arithmetic/Funs.lean"),
    MUL: "bridge/Arithmetic/PortableGenerated.lean",
}
BINDINGS = {
    "core.slice.Slice.split_last": "splitLast",
    "core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.fold": "reverseFold",
}
ARTIFACTS = {f"{EXTRACTION}/{name}" for name in
             ("arithmetic.llbc", "charon.log", "aeneas.log", "Arithmetic/Funs.lean",
              "Arithmetic/Types.lean", "Arithmetic/FunsExternal_Template.lean",
              "Arithmetic/TypesExternal_Template.lean")}
HEADER = """-- Exact original source declarations. Local notation binds the scoped std runtime.
module
public import Arithmetic.PortableHornerRuntime
public import Arithmetic.PortableGenerated
public import Arithmetic.PortableXorGenerated
public import Arithmetic.DenseNormalizationGenerated
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace bulksketch

""" + "".join(
    f'local notation "{source}" => Aeneas.Std.PortableHornerRuntime.{model}\n'
    for source, model in BINDINGS.items()
) + "\n"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def blocks(path):
    body = path.read_text().split("namespace bulksketch\n", 1)[1].rsplit("end bulksketch", 1)[0]
    result = {}
    for block in re.findall(r"(?ms)^/--.*?(?=^/--|\Z)", body):
        declarations = re.findall(r"(?m)^(?:def|impl_def|structure|inductive)\s+(\S+)", block)
        if len(declarations) != 1 or declarations[0] in result:
            raise ValueError("unrecognized or duplicate declaration in " + str(path))
        result[declarations[0]] = block
    return result


def projection(root):
    types = blocks(root / EXTRACTION / "Arithmetic/Types.lean")
    functions = blocks(root / EXTRACTION / "Arithmetic/Funs.lean")
    if list(types) != TYPES or list(functions) != [*SHARED, *FUNCTIONS]:
        raise ValueError("Portable Horner raw declaration set changed")
    compiled_types = blocks(root / "bridge/Arithmetic/Types.lean")
    for name in TYPES[:-1]:
        if types[name].rstrip() != compiled_types[name].rstrip():
            raise ValueError("shared Portable Horner type differs: " + name)
    for name, source in SHARED.items():
        if functions[name].rstrip() != blocks(root / source)[name].rstrip():
            raise ValueError("shared Portable Horner declaration differs: " + name)
    return HEADER + types[CLOSURE].rstrip() + "\n\n" + "".join(
        functions[name] for name in FUNCTIONS) + "end bulksketch\n"


def check(root=ROOT):
    receipt = json.loads((root / EXTRACTION / "receipt.json").read_text())
    if receipt["status"] != "generated" or receipt["llbc_has_errors"] is not False:
        raise ValueError("Portable Horner extraction is incomplete")
    if len(receipt["artifacts"]) != len(ARTIFACTS) or \
            {item["path"] for item in receipt["artifacts"]} != ARTIFACTS:
        raise ValueError("Portable Horner raw artifact set changed")
    for item in receipt["artifacts"]:
        if sha(root / item["path"]) != item["sha256"]:
            raise ValueError("Portable Horner raw artifact mismatch: " + item["path"])
    refinement = json.loads((root / EXTRACTION / "refinement-receipt.json").read_text())
    if sha(root / RUNTIME) != refinement["files_sha256"][RUNTIME]:
        raise ValueError("scoped Portable Horner runtime mismatch")
    if (root / COMPILED).read_text() != projection(root):
        raise ValueError("compiled Portable Horner projection differs")
    raw = EXTRACTION + "/Arithmetic/Funs.lean"
    return {"raw_generated_file": raw, "raw_file_sha256": sha(root / raw),
            "shared_types_and_function_dictionary_declarations_checked": True,
            "compiled_projection": COMPILED, "projection_file_sha256": sha(root / COMPILED),
            "source_declarations_retained_verbatim": len(FUNCTIONS),
            "source_type_declarations_retained_verbatim": 1,
            "shared_declarations_checked": len(SHARED) + len(TYPES) - 1,
            "scoped_standard_library_bindings": BINDINGS,
            "scoped_runtime_file": RUNTIME, "scoped_runtime_sha256": sha(root / RUNTIME),
            "generated_declarations": ["bulksketch." + name for name in FUNCTIONS]}


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
