#!/usr/bin/env python3
"""Verify the exact original Dense modular square projection."""
import importlib.util
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
COMMON = importlib.util.spec_from_file_location("dense_reducer_table", ROOT / "extraction/dense-reducer-table/project.py")
table = importlib.util.module_from_spec(COMMON)
COMMON.loader.exec_module(table)
require, sha, declarations = table.require, table.sha, table.declarations
shared = table.shared
CONTROLS, ENVIRONMENT, FLAGS, NAMES = table.CONTROLS, table.ENVIRONMENT, table.FLAGS, table.NAMES

EXTRACTION = Path("extraction/dense-reducer-square")
RAW = EXTRACTION / "Arithmetic"
ACTIVE = Path("bridge/Arithmetic/DenseReducerSquareGenerated.lean")
RUNTIME = Path("bridge/Arithmetic/DenseReducerSquareRuntime.lean")
PATCH = EXTRACTION / "checked-dense-reducer-square.patch"
DENSE_MUL_PATCH = Path("tooling/aeneas-dense-mul/shared-loop-erasure.patch")
SELECTOR = "{impl bulksketch::poly::Polynomial for bulksketch::poly::Dense}::square_mod_into"
VARIANT = "checked-dense-reducer-square-v1"
PATCHED_BINARY_SHA256 = '4bf7c2b3989fae2d12239f89158ba088b732a4ff6d332d4d51b47e02ce76c365'
BASE_SOURCES = {'src/interp/InterpExpansion.ml': 'c3672499de02ee3ed411bbbe2f6a85e7a24c33df9ec12b84e409327b4c6fc6dc', 'src/interp/InterpMatchCtxs.ml': 'a97bd2650a71ec0795f570dac17a8a1f1f52ae2b6feb4619984e6f1d61fde264', 'src/symbolic/SymbolicToPureExpressions.ml': '250813689915257fcab9850a12804d6a0b3a6f7ec5dd7a854dd33a849419c023'}
PATCHED_SOURCES = {'src/interp/InterpExpansion.ml': 'a6f3b2621f0836c20add44395fad2ccac5e350aa51bf5d670d593e22f1d35df0', 'src/interp/InterpMatchCtxs.ml': 'b250146dc8d9a8ce2d9ea24e1e959e45a82e0138e4d92f328c87eb8468c037e1', 'src/symbolic/SymbolicToPureExpressions.ml': 'ce26b83927530c663e28448d734dcc07a5a6f422ba67e1b4895d8c58eda7f7a4'}
FUNCTION = "poly.Dense.Insts.BulksketchPolyPolynomial.square_mod_into"
FUNCTIONS = tuple(FUNCTION + suffix for suffix in (
    "_loop0_loop0.body", "_loop0_loop0", "_loop0.body", "_loop0",
    "_loop1.body", "_loop1", "",
))
ARTIFACTS = {
    PATCH,
    EXTRACTION / "arithmetic.llbc",
    EXTRACTION / "charon.log",
    EXTRACTION / "axioms.log",
    EXTRACTION / "Axioms.lean",
    *(RAW / name for name in NAMES),
    *(EXTRACTION / (name + ".log") for name in CONTROLS),
}
HEADER = """-- Exact original Dense modular squaring and its six loop declarations.
import Arithmetic.DenseReducerSquareRuntime
import Arithmetic.DenseMulConvolutionGenerated

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false
set_option maxRecDepth 4096

namespace bulksketch

local notation "core.slice.Slice.last" => DenseReducerTableRuntime.last
local notation "core.option.Option.Insts.CoreCmpPartialEqOption.eq" => DenseReducerTableRuntime.optionEq
local notation "core.num.Usize.div_ceil" => DenseReducerSquareRuntime.divCeil

"""


def sections(path):
    raw = path.read_text()
    records = re.findall(r"(?ms)^diff --git a/(\S+) b/(\S+)\n(.*?)(?=^diff --git|\Z)", raw)
    require(records and all(before == after for before, after, _ in records)
            and len({before for before, _, _ in records}) == len(records),
            "invalid Dense reducer patch file headers")
    return {before: body for before, _, body in records}


def check(root=ROOT):
    receipt = json.loads((root / EXTRACTION / "receipt.json").read_text())
    require(receipt["source_commit"] == shared.SOURCE and receipt["selector"] == SELECTOR
            and receipt["target"] == shared.TARGET and receipt["rust_toolchain"] == "nightly-2026-09-17"
            and receipt["aeneas_commit"] == shared.AENEAS and receipt["charon_commit"] == shared.CHARON
            and receipt["variant_id"] == VARIANT and receipt["native_source_edited"] is False
            and receipt["base_binary_sha256"] == shared.BINARY_SHA256
            and receipt["patched_binary_sha256"] == PATCHED_BINARY_SHA256
            and receipt["base_sources"] == BASE_SOURCES and receipt["modified_sources"] == PATCHED_SOURCES
            and set(receipt["files_sha256"]) == {str(path) for path in ARTIFACTS},
            "invalid Dense modular square receipt")
    for path, expected in receipt["files_sha256"].items():
        require(sha(root / path) == expected, "Dense modular square artifact differs: " + path)
    exact_patches = sections(root / DENSE_MUL_PATCH) | sections(root / table.PATCH)
    require(receipt["variant_patch"] == str(PATCH) and receipt["variant_patch_sha256"] == sha(root / PATCH)
            and sections(root / PATCH) == exact_patches,
            "Dense modular square patch differs from its three reviewed parts")

    capture = receipt["charon_command"]
    parent = json.loads((root / "extraction/root-setup/receipt.json").read_text())
    manifest = next(word for word in parent["charon_command"] if word.startswith("--manifest-path="))
    source_root = Path(manifest.removeprefix("--manifest-path=")).parent
    input_capture = str(source_root.parent /
                        "bulksketch-proof-evidence-20261109-root-traversal/dense-square-mod/arithmetic.llbc")
    evidence = source_root.parent / "bulksketch-proof-evidence-20261109-dense-reducer/dense-square-mod"
    require(capture[0] == parent["charon_command"][0] and
            capture[1:4] == ["cargo", "--preset=aeneas", "--sysroot=default"] and
            capture[4] == "--dest-file=" + input_capture and
            capture[5:] == ["--start-from=" + SELECTOR, "--", manifest,
                            "-p", "bulksketch", "--lib", "--locked", "--target", shared.TARGET],
            "Dense modular square Charon command differs")
    commands = receipt["commands"]
    require(set(commands) == set(CONTROLS), "Dense modular square control set differs")
    patched_binary = commands["checked"]["command"][0]
    require(Path(patched_binary) == source_root.parent /
                "bulksketch-proof-tools/aeneas-dense-reducer-square/src/_build/default/main.exe",
            "Dense modular square patched binary identity differs")
    stock_binary = str(source_root / "verification/lean/tooling/aeneas/src/_build/default/main.exe")
    dest_name = {"checked": "level-one", "portable-xor": "final-xor", "portable-xor-stock": "final-xor-stock"}
    for name, (enabled, checked, status) in CONTROLS.items():
        command = commands[name]["command"]
        expected_binary = stock_binary if name in ("stock", "portable-xor-stock") else patched_binary
        flags = ([*FLAGS[:2], "-checks", *FLAGS[2:]] if name == "checked" else
                 [*FLAGS, *(["-checks"] if checked else [])])
        is_xor = name.startswith("portable-xor")
        input_path = "extraction/portable-xor/arithmetic.llbc" if is_xor else str(EXTRACTION / "arithmetic.llbc")
        require(command[0] == expected_binary and command[1:-3] == flags and command[-3] == "-dest"
                and Path(command[-2]) == evidence / dest_name.get(name, "final-" + name)
                and command[-1] == (str(source_root / "verification/lean" / input_path) if is_xor else input_capture)
                and commands[name]["exit_code"] == status
                and commands[name]["environment"] == (ENVIRONMENT if enabled else {})
                and commands[name]["input_sha256"] == sha(root / input_path),
                "Dense modular square checked command or control differs: " + name)
        output = (root / EXTRACTION / (name + ".log")).read_text()
        if status:
            require("Could not match the contexts" in output and "lines 213:16-217:17" in output,
                    "Dense modular square control lost its original join rejection: " + name)
        else:
            require("Generated the partial file" not in output and "Error" not in output,
                    "Dense modular square successful extraction was partial: " + name)

    exact = {name: sha(root / RAW / name) for name in NAMES}
    require(commands["checked"]["outputs"] == exact and commands["replay"]["outputs"] == exact
            and set(commands["portable-xor"]["outputs"]) == set(NAMES)
            and commands["portable-xor"]["outputs"] == commands["portable-xor-stock"]["outputs"],
            "Dense modular square replay bytes differ")

    llbc = json.loads((root / EXTRACTION / "arithmetic.llbc").read_text())
    translated = llbc["translated"]
    options = translated["options"]
    targets = translated["target_information"]
    require(llbc["has_errors"] is False and options["start_from"] == [SELECTOR]
            and options["opaque"] == [] and options["dest_file"] == input_capture
            and len(targets) == 1 and targets[0]["key"] == shared.TARGET
            and targets[0]["value"]["target_pointer_size"] == 8, "Dense modular square LLBC scope differs")
    bodies = {}
    for f in translated["fun_decls"]:
        if f:
            meta = f["item_meta"]
            name = meta["name"][-1].get("Ident", [None])[0]
            if name in ("square_mod_into", "normalized_len"):
                require(name not in bodies and "Structured" in f["body"], "Dense modular square original body missing")
                span = meta["span"]["Untagged"]["data"]
                source = translated["files"][span["file_id"]]
                require(source["name"] == {"Local": table.SOURCE}
                        and source["contents"].encode() == (root.parents[1] / table.SOURCE).read_bytes()
                        and sha(root.parents[1] / table.SOURCE) == table.SOURCE_SHA256, "original Dense square source differs")
                bodies[name] = (span["beg"]["line"], span["beg"]["col"], span["end"]["line"], span["end"]["col"])
    require(bodies == {"square_mod_into": (188, 4, 224, 5), "normalized_len": (227, 0, 232, 1)},
            "Dense modular square original declaration spans differ")

    types = declarations(root / RAW / "Types.lean")
    shared_types = {
        "bridge/Arithmetic/Types.lean": {"types.RawProduct", "types.FieldId", "field.sealed.Sealed", "field.BinaryField"},
        "bridge/Arithmetic/SliceKernelTypes.lean": {"backend.contract.Arithmetic", "backend.contract.BulkKernels"},
        "bridge/Arithmetic/DenseNormalizationTypes.lean": {"poly.dense.normalized_len.closure_1", "poly.dense.normalized_len.closure"},
    }
    require(set(types) == set().union(*shared_types.values()), "Dense modular square shared type set differs")
    for path, names in shared_types.items():
        current = (root / path).read_text()
        require(all(types[name] in current for name in names), "Dense modular square shared type differs: " + path)
    functions = declarations(root / RAW / "Funs.lean")
    normalizer = declarations(root / "bridge/Arithmetic/DenseNormalizationGenerated.lean")
    clone = declarations(root / "bridge/Arithmetic/DenseMulConvolutionGenerated.lean")
    raw_default = declarations(root / "bridge/Arithmetic/OddRecurrenceGenerated.lean")
    require({name: block for name, block in functions.items() if name.startswith("poly.dense.normalized_len")} ==
            {name: block for name, block in normalizer.items() if name.startswith("poly.dense.normalized_len")}
            and all(functions[name] == clone.get(name) for name in (
                "types.RawProduct.Insts.CoreCloneClone.clone", "types.RawProduct.Insts.CoreCloneClone"))
            and functions["types.RawProduct.Insts.CoreDefaultDefault.default"] ==
                raw_default["types.RawProduct.Insts.CoreDefaultDefault.default"],
            "Dense modular square shared source function differs")
    expected = HEADER + "\n\n".join(functions[name] for name in FUNCTIONS) + "\n\nend bulksketch\n"
    require((root / ACTIVE).read_text() == expected, "compiled Dense modular square projection differs")
    require(sha(root / RUNTIME) == receipt["runtime_sha256"], "Dense modular square scoped runtime differs")
    permitted = {"propext", "Classical.choice", "Quot.sound"}
    axioms = re.findall(r"depends on axioms: \[([^\]]*)\]", (root / EXTRACTION / "axioms.log").read_text())
    require(len(axioms) == 4 and all({part.strip() for part in row.split(",")} <= permitted for row in axioms),
            "Dense modular square axioms differ")
    return {
        "raw_generated_file": str(RAW / "Funs.lean"), "raw_file_sha256": sha(root / RAW / "Funs.lean"),
        "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
        "source_declarations_retained_verbatim": len(FUNCTIONS),
        "shared_types_and_function_dictionary_declarations_checked": True,
        "generated_declarations": ["bulksketch." + name for name in FUNCTIONS],
        "translator_variant": VARIANT,
        "native_source_edited": False,
    }


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
