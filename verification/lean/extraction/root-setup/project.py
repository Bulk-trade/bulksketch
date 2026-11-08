#!/usr/bin/env python3
"""Check the stock Aeneas projection of original root traversal setup."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/root-setup")
RAW = DIRECTORY / "Arithmetic"
ACTIVE = Path("bridge/Arithmetic/RootSetupGenerated.lean")
SELECTORS = ["bulksketch::decode::roots::_::" + name for name in
             ("new", "start", "enable_v3", "enable_closed_form", "set_splitter_seed")]
SOURCE = "0a5bda53f6b07fcae8acd870e2d0c4a246d207e6"
TARGET = "x86_64-apple-darwin"
CHARON = "7b462d9159db2ed3015162352183906a30bfafc6"
AENEAS = "ab34bd28458a08c150b7cbf1873e59af74588138"
BINARY_SHA256 = {
    "aeneas": "91f5a2776a79e2923517a2c4807c9fc017e79f185ae490502247f16e2941e330",
    "charon": "913e7969d1a0296038d115bcf1af47f8c0c6702266cc7a78a02a2b4ad7a0dfbe",
}
FLAGS = ["-backend", "lean", "-checks", "-sequential", "-no-progress-bar",
         "-print-error-emitters", "-split-files", "-dest"]
SOURCE_SHA256 = {
    "src/decode/roots.rs": "4697d5874fd1eb03c0210371fdac83a8dc7171de2724da046613f59c879f4fb6",
    "src/decode/affine.rs": "a7c45498717202aec291b4c4acdd6f819edf16bcdf478500a8c74a3492c4e11d",
    "src/decode/scratch.rs": "97016cadabf021829b567ff1472a9f11136f54059d78e457d58896cc318e50f6",
    "src/field/mod.rs": "035dc6193ebb50b324527525c0ee47cbe06ca325db16aa5f8ee55b0e79baa723",
    "src/types.rs": "5702a8552c1158cf69f2155d2484f246f87475dc6bef3ea734be52348acd940d",
}
SPANS = {
    "src/decode/roots.rs": {
        "new": (49, 68), "enable_v3": (74, 76), "enable_closed_form": (78, 80),
        "set_splitter_seed": (82, 84), "start": (86, 98), "stage": (99, 109),
    },
    "src/decode/affine.rs": {
        "square_products": (22, 24), "predicted_affine": (26, 48),
        "PREFERRED_MASK": (52, 62), "preferred": (64, 66),
    },
}
AFFINE = ["decode.affine." + name for name in (
    "square_products", "predicted_affine_loop0_loop0.body", "predicted_affine_loop0_loop0",
    "predicted_affine_loop0.body", "predicted_affine_loop0", "predicted_affine",
    "PREFERRED_MASK_loop.body", "PREFERRED_MASK_loop", "PREFERRED_MASK", "preferred",
)]
FUNCTIONS = ["decode.roots.FactorWork.new", *AFFINE, *["decode.roots.Roots." + name for name in
             ("enable_v3", "enable_closed_form", "set_splitter_seed", "start")]]
FACTOR_WORK = "decode.roots.FactorWork"
SHARED_TYPES = {
    "Arithmetic/Types.lean": {"types.RawProduct", "types.FieldId", "field.sealed.Sealed",
                              "field.BinaryField", "field.Gf64"},
    "Arithmetic/RebuiltLfsrTypes.lean": {"core.ops.range.RangeToInclusive"},
    "Arithmetic/ReconstructionTypes.lean": {"types.Stage",
        "decode.roots.Roots", "decode.scratch.SplitterBasis", "decode.scratch.FactorFrame",
        "decode.scratch.RowWorkspace"},
}
FIELD_FUNS = {
    "field.Gf64.Insts." + suffix for suffix in (
        "BulksketchFieldBinaryField", "BulksketchFieldBinaryField.BITS",
        "BulksketchFieldBinaryField.MODULUS_LOW", "BulksketchFieldBinaryField.WIRE_ID",
        "BulksketchFieldBinaryField.MASK", "BulksketchFieldSealedSealed", "CoreCmpEq",
        "CoreCmpEq.assert_fields_are_eq", "CoreCmpPartialEqGf64", "CoreCmpPartialEqGf64.eq",
        "CoreCloneClone", "CoreCloneClone.clone", "CoreMarkerCopy",
    )
}
INCLUSIVE = "core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice"
ARTIFACTS = {str(DIRECTORY / name) for name in (
    "arithmetic.llbc", "charon.log", "aeneas.log", "replay.log", "Arithmetic/Funs.lean",
    "Arithmetic/FunsExternal_Template.lean", "Arithmetic/Types.lean",
)}
HEADER = """-- Original checked root setup declarations with scoped library bindings.
import Arithmetic.ClosedLeafGenerated
import Arithmetic.VerifyDispatchRuntime

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxRecDepth 2048

namespace bulksketch

local notation "core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice" =>
  RebuiltLfsrRuntime.inclusive

"""


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def declarations(path):
    body = path.read_text().split("namespace bulksketch\n", 1)[1].rsplit("end bulksketch", 1)[0]
    result = {}
    for block in re.findall(r"(?ms)^/--.*?(?=^/--|\Z)", body):
        names = re.findall(r"(?m)^(?:def|impl_def|structure|inductive|abbrev)\s+(\S+)", block)
        require(len(names) == 1 and names[0] not in result, "invalid declaration block: " + str(path))
        result[names[0]] = block.strip()
    return result


def projected(types, functions):
    return HEADER + "\n\n".join([types[FACTOR_WORK], *(functions[name] for name in FUNCTIONS)]) + "\n\nend bulksketch\n"


def check_receipt(root, receipt):
    require(receipt["source_commit"] == SOURCE and receipt["selectors"] == SELECTORS
            and receipt["target"] == TARGET and receipt["rust_toolchain"] == "nightly-2026-09-17"
            and receipt["aeneas_commit"] == AENEAS and receipt["charon_commit"] == CHARON
            and receipt["binary_sha256"] == BINARY_SHA256 and receipt["native_source_edited"] is False
            and receipt["opaque_application_bodies"] == [] and receipt["checked_exit"] == 0
            and receipt["sources_sha256"] == SOURCE_SHA256
            and set(receipt["files_sha256"]) == ARTIFACTS, "invalid root setup receipt")
    for path, expected in receipt["files_sha256"].items():
        require(sha(root / path) == expected, "root setup artifact differs: " + path)
    ch = receipt["charon_command"]
    ae = receipt["aeneas_command"]
    replay = receipt["replay"]
    require(Path(ch[0]).parts[-4:] == ("tooling", "charon", "bin", "charon")
            and ch[1:4] == ["cargo", "--preset=aeneas", "--sysroot=default"]
            and ch[4].startswith("--dest-file=")
            and ch[5:11] == [*("--start-from=" + name for name in SELECTORS), "--"]
            and ch[11].startswith("--manifest-path=")
            and ch[12:] == ["-p", "bulksketch", "--lib", "--locked", "--target", TARGET],
            "root setup recorded Charon command differs")
    destination = Path(ch[4].removeprefix("--dest-file="))
    require(destination.parts[-2:] == ("root-setup", "arithmetic.llbc")
            and Path(ae[0]).parts[-6:] == ("tooling", "aeneas", "src", "_build", "default", "main.exe")
            and ae[1:-2] == FLAGS and Path(ae[-1]) == destination
            and Path(ae[-2]) == destination.parent / "stock"
            and replay["command"] == [*ae[:-2], str(destination.parent / "replay"), ae[-1]]
            and replay["exit_code"] == 0
            and replay["input_sha256"] == sha(root / DIRECTORY / "arithmetic.llbc")
            and replay["log_sha256"] == sha(root / DIRECTORY / "replay.log")
            and replay["outputs"] == {name: sha(root / RAW / name) for name in
                                       ("Funs.lean", "FunsExternal_Template.lean", "Types.lean")},
            "root setup checked replay differs")


def check_llbc(root):
    llbc = json.loads((root / DIRECTORY / "arithmetic.llbc").read_text())
    translated = llbc["translated"]
    require(llbc["has_errors"] is False and translated["options"]["start_from"] == SELECTORS
            and translated["options"]["opaque"] == [], "root setup LLBC closure differs")
    targets = translated["target_information"]
    require(len(targets) == 1 and targets[0]["key"] == TARGET
            and targets[0]["value"]["target_pointer_size"] == 8, "root setup target differs")
    observed = {}
    for entry in translated["files"]:
        if not entry:
            continue
        path = entry["name"].get("Local")
        if path in SOURCE_SHA256:
            require(path not in observed, "duplicate LLBC source: " + path)
            observed[path] = hashlib.sha256(entry["contents"].encode()).hexdigest()
    require(observed == SOURCE_SHA256, "root setup embedded source differs")
    for path, expected in SOURCE_SHA256.items():
        require(sha(root.parents[1] / path) == expected, "root setup source differs: " + path)
    found = {}
    for function in translated["fun_decls"]:
        if not function:
            continue
        meta = function["item_meta"]
        name = meta["name"][-1].get("Ident", [""])[0]
        span = meta["span"]["Untagged"]["data"]
        path = translated["files"][span["file_id"]]["name"].get("Local")
        if path not in SPANS or name not in SPANS[path]:
            continue
        key = (path, name)
        require(key not in found and "Structured" in function["body"]
                and (span["beg"]["line"], span["end"]["line"]) == SPANS[path][name],
                "root setup source body differs: " + name)
        found[key] = function
    require(set(found) == {(path, name) for path, spans in SPANS.items() for name in spans},
            "root setup source body missing")


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    check_receipt(root, receipt)
    check_llbc(root)
    types = declarations(root / RAW / "Types.lean")
    shared_types = {name for names in SHARED_TYPES.values() for name in names}
    require(set(types) == shared_types | {FACTOR_WORK}, "root setup type set differs")
    for path, names in SHARED_TYPES.items():
        existing = declarations(root / "bridge" / path)
        require(all(types[name] == existing.get(name) for name in names), "root setup shared type differs: " + path)
    functions = declarations(root / RAW / "Funs.lean")
    stage = "decode.roots.Roots.stage"
    require(set(functions) == set(FUNCTIONS) | FIELD_FUNS | {INCLUSIVE, stage},
            "root setup declaration set differs")
    field = declarations(root / "bridge/Arithmetic/Funs.lean")
    closed_leaf = declarations(root / "bridge/Arithmetic/ClosedLeafGenerated.lean")
    require(all(functions[name] == field.get(name) for name in FIELD_FUNS)
            and functions[stage] == closed_leaf[stage], "root setup shared function body differs")
    externals = (root / RAW / "FunsExternal_Template.lean").read_text()
    names = set(re.findall(r"(?m)^axiom\s+(\S+)", externals))
    require(names == {"core.num.U64.div_ceil", *(INCLUSIVE + "." + name for name in
        ("get", "get_mut", "get_unchecked", "get_unchecked_mut", "index", "index_mut"))},
        "unexpected root setup external binding")
    require((root / ACTIVE).read_text() == projected(types, functions), "compiled root setup projection differs")
    return {
        "raw_generated_file": str(RAW / "Funs.lean"), "raw_file_sha256": sha(root / RAW / "Funs.lean"),
        "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
        "source_declarations_retained_verbatim": len(FUNCTIONS) + 1,
        "shared_types_and_function_dictionary_declarations_checked": True,
        "generated_declarations": ["bulksketch." + name for name in (FACTOR_WORK, *FUNCTIONS)],
        "native_source_edited": False,
    }


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
