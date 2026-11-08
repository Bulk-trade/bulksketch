#!/usr/bin/env python3
"""Verify the PCLMUL maps projection and byte-exact generated dependencies."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
EXTRACTION = "extraction/pclmul-next"
COMPILED = "bridge/Arithmetic/X86PclmulNextGenerated.lean"
BASE = "backend.x86_pclmul."
ENTRY = BASE + "Pclmul.Insts.BulksketchBackendContractArithmetic."
INVERSE = BASE + "inverse"
SELECTED_ROOTS = [
    "{impl bulksketch::backend::contract::Arithmetic for "
    "bulksketch::backend::x86_pclmul::Pclmul}::" + name
    for name in ("frobenius", "inverse", "solve_quadratic")
]
CLOSURE_TYPES = [INVERSE + suffix for suffix in (".closure_2", ".closure_1", ".closure")]
SHARED_TYPES = ["types.FieldId", "field.sealed.Sealed", "field.BinaryField", "types.RawProduct"]
FUNCTIONS = [
    *(BASE + name for name in ("frobenius_loop0.body", "frobenius_loop0",
        "frobenius_loop1.body", "frobenius_loop1", "frobenius")),
    ENTRY + "frobenius",
    CLOSURE_TYPES[0] + ".Insts.CoreOpsFunctionFnTupleU64U64.call",
    *(CLOSURE_TYPES[1] + ".Insts.CoreOpsFunction" + name for name in (
        "FnPairU64U32U64.call", "FnMutPairU64U32U64.call_mut", "FnOncePairU64U32U64.call_once",
        "FnOncePairU64U32U64", "FnMutPairU64U32U64", "FnPairU64U32U64")),
    *(CLOSURE_TYPES[2] + ".Insts.CoreOpsFunction" + name for name in (
        "FnPairU64U64U64.call", "FnMutPairU64U64U64.call_mut", "FnOncePairU64U64U64.call_once",
        "FnOncePairU64U64U64", "FnMutPairU64U64U64", "FnPairU64U64U64")),
    INVERSE, ENTRY + "inverse", BASE + "solve_quadratic", ENTRY + "solve_quadratic",
]
SHARED = {
    "Funs": 20,
    "X86PclmulGenerated": 5,
    "FrobeniusConstGenerated": 5,
    "FrobeniusTablesGenerated": 37,
    "InverseGenerated": 3,
}
ARTIFACTS = {f"{EXTRACTION}/{name}" for name in
    ("arithmetic.llbc", "charon.log", "aeneas.log", "Arithmetic/Funs.lean",
     "Arithmetic/Types.lean", "Arithmetic/FunsExternal_Template.lean",
     "Arithmetic/TypesExternal_Template.lean")}
HEADER = """-- Exact original PCLMUL maps declarations and verified generated dependencies.
import Arithmetic.X86PclmulGenerated
import Arithmetic.FrobeniusTablesGenerated
import Arithmetic.InverseGenerated

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace bulksketch

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
    functions = blocks(root / EXTRACTION / "Arithmetic/Funs.lean")
    retained = [name for name in functions if name in FUNCTIONS]
    if list(types) != SHARED_TYPES + CLOSURE_TYPES or retained != FUNCTIONS:
        raise ValueError("PCLMUL maps declaration set changed")
    shared_types = blocks(root / "bridge/Arithmetic/Types.lean")
    for name in SHARED_TYPES:
        if types[name].rstrip() != shared_types[name].rstrip():
            raise ValueError("shared PCLMUL type differs: " + name)

    shared_files = {name: blocks(root / f"bridge/Arithmetic/{name}.lean") for name in SHARED}
    counts = dict.fromkeys(SHARED, 0)
    for name, block in functions.items():
        if name in FUNCTIONS:
            continue
        matches = [file for file, declarations in shared_files.items()
                   if name in declarations and block.rstrip() == declarations[name].rstrip()]
        if len(matches) != 1:
            raise ValueError("shared PCLMUL declaration differs or is ambiguous: " + name)
        counts[matches[0]] += 1
    if counts != SHARED:
        raise ValueError("shared PCLMUL declaration counts changed")

    return HEADER + "".join(types[name].rstrip() + "\n\n" for name in CLOSURE_TYPES) + "".join(
        functions[name] for name in FUNCTIONS) + "end bulksketch\n"


def check(root=ROOT):
    receipt = json.loads((root / EXTRACTION / "receipt.json").read_text())
    if receipt["status"] != "generated" or receipt["llbc_has_errors"] is not False:
        raise ValueError("PCLMUL maps extraction is incomplete")
    if len(receipt["artifacts"]) != len(ARTIFACTS) or \
            {item["path"] for item in receipt["artifacts"]} != ARTIFACTS:
        raise ValueError("PCLMUL maps raw artifact set changed")
    for item in receipt["artifacts"]:
        if sha(root / item["path"]) != item["sha256"]:
            raise ValueError("PCLMUL maps raw artifact mismatch: " + item["path"])
    llbc = json.loads((root / EXTRACTION / "arithmetic.llbc").read_text())
    if llbc["has_errors"] is not False or \
            llbc["translated"]["options"]["start_from"] != SELECTED_ROOTS or \
            receipt["selected_roots"] != SELECTED_ROOTS or receipt["target"] != "x86_64-apple-darwin":
        raise ValueError("PCLMUL maps LLBC selection differs")
    if (root / COMPILED).read_text() != projection(root):
        raise ValueError("compiled PCLMUL maps projection differs")
    raw = EXTRACTION + "/Arithmetic/Funs.lean"
    return {"raw_generated_file": raw, "raw_file_sha256": sha(root / raw),
            "compiled_projection": COMPILED, "projection_file_sha256": sha(root / COMPILED),
            "source_declarations_retained_verbatim": len(FUNCTIONS),
            "source_type_declarations_retained_verbatim": len(CLOSURE_TYPES),
            "shared_types_and_function_dictionary_declarations_checked": True,
            "shared_declarations_checked": sum(SHARED.values()) + len(SHARED_TYPES),
            "generated_declarations": ["bulksketch." + name for name in FUNCTIONS]}


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
