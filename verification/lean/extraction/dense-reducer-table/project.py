#!/usr/bin/env python3
"""Check exact native Dense reducer-table extraction and its runtime bindings."""
import importlib.util
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
COMMON = importlib.util.spec_from_file_location("root_setup", ROOT / "extraction/root-setup/project.py")
shared = importlib.util.module_from_spec(COMMON)
COMMON.loader.exec_module(shared)
require, sha, declarations = shared.require, shared.sha, shared.declarations

EXTRACTION = Path("extraction/dense-reducer-table")
RAW = EXTRACTION / "Arithmetic"
ACTIVE = Path("bridge/Arithmetic/DenseReducerTableGenerated.lean")
RUNTIME = Path("bridge/Arithmetic/DenseReducerTableRuntime.lean")
PATCH = EXTRACTION / "checked-dense-reducer-option.patch"
SOURCE = "src/poly/dense.rs"
SOURCE_SHA256 = "13b360fba6387dda36a9655f3f67d01be6752e4ca6b7f8e1824e7333bf3da644"
SELECTOR = "{impl bulksketch::poly::Polynomial for bulksketch::poly::Dense}::prepare_square_table"
VARIANT = "checked-dense-reducer-option-v1"
ENVIRONMENT = {"BULKSKETCH_DENSE_REDUCER": "1"}
PATCHED_BINARY_SHA256 = "282f3f7a0dfa84185fb4a376a42bb40510a83a5e625a1aed64667eb570857122"
MATCHER = "src/interp/InterpMatchCtxs.ml"
BASE_MATCHER_SHA256 = "a97bd2650a71ec0795f570dac17a8a1f1f52ae2b6feb4619984e6f1d61fde264"
PATCHED_MATCHER_SHA256 = "b250146dc8d9a8ce2d9ea24e1e959e45a82e0138e4d92f328c87eb8468c037e1"
FUNCTION = "poly.Dense.Insts.BulksketchPolyPolynomial.prepare_square_table"
FUNCTIONS = (FUNCTION + "_loop.body", FUNCTION + "_loop", FUNCTION)
SHIFT = "poly.dense.times_x_mod"
RANGE = "core.ops.range.RangeTo.Insts.CoreOpsRangeRangeBounds"
NAMES = ("Funs.lean", "FunsExternal_Template.lean", "Types.lean")
FLAGS = ("-backend", "lean", "-sequential", "-no-progress-bar",
         "-print-error-emitters", "-split-files")
CONTROLS = {
    "checked": (True, True, 0),
    "replay": (True, True, 0),
    "stock": (False, True, 1),
    "disabled": (False, True, 1),
    "unchecked": (True, False, 1),
    "portable-xor": (True, True, 0),
    "portable-xor-stock": (False, True, 0),
}
ARTIFACTS = {
    PATCH,
    EXTRACTION / "arithmetic.llbc",
    EXTRACTION / "charon.log",
    EXTRACTION / "axioms.log",
    EXTRACTION / "Axioms.lean",
    *(RAW / name for name in NAMES),
    *(EXTRACTION / (name + ".log") for name in CONTROLS),
}
HEADER = """-- Exact original Dense square-table preparation and its loop.
import Arithmetic.DenseReducerTableRuntime

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false

namespace bulksketch

local notation "core.slice.Slice.last" => DenseReducerTableRuntime.last
local notation "core.option.Option.Insts.CoreCmpPartialEqOption.eq" => DenseReducerTableRuntime.optionEq

"""


def check(root=ROOT):
    receipt = json.loads((root / EXTRACTION / "receipt.json").read_text())
    require(receipt["source_commit"] == shared.SOURCE and receipt["selector"] == SELECTOR
            and receipt["target"] == shared.TARGET and receipt["rust_toolchain"] == "nightly-2026-09-17"
            and receipt["aeneas_commit"] == shared.AENEAS and receipt["charon_commit"] == shared.CHARON
            and receipt["variant_id"] == VARIANT and receipt["native_source_edited"] is False
            and receipt["base_binary_sha256"] == shared.BINARY_SHA256
            and receipt["patched_binary_sha256"] == PATCHED_BINARY_SHA256
            and receipt["base_sources"] == {MATCHER: BASE_MATCHER_SHA256}
            and receipt["modified_sources"] == {MATCHER: PATCHED_MATCHER_SHA256}
            and set(receipt["files_sha256"]) == {str(path) for path in ARTIFACTS},
            "invalid Dense reducer table receipt")
    for path, expected in receipt["files_sha256"].items():
        require(sha(root / path) == expected, "Dense reducer table artifact differs: " + path)

    patch = (root / PATCH).read_text()
    require(receipt["variant_patch"] == str(PATCH) and receipt["variant_patch_sha256"] == sha(root / PATCH)
            and re.findall(r"(?m)^diff --git a/(\S+) b/(\S+)$", patch) ==
                [("src/interp/InterpMatchCtxs.ml", "src/interp/InterpMatchCtxs.ml")],
            "Dense reducer translator patch scope differs")
    capture = receipt["charon_command"]
    parent = json.loads((root / "extraction/root-setup/receipt.json").read_text())
    manifest = next(word for word in parent["charon_command"] if word.startswith("--manifest-path="))
    source_root = Path(manifest.removeprefix("--manifest-path=")).parent
    evidence = source_root.parent / "bulksketch-proof-evidence-20261109-dense-reducer" / "final-controls"
    capture_file = source_root.parent / "bulksketch-proof-evidence-20261109-root-traversal/dense-square-table/arithmetic.llbc"
    require(capture[0] == parent["charon_command"][0] and
            capture[1:4] == ["cargo", "--preset=aeneas", "--sysroot=default"] and
            capture[4] == "--dest-file=" + str(capture_file) and
            capture[5:] == ["--start-from=" + SELECTOR, "--", manifest,
                            "-p", "bulksketch", "--lib", "--locked", "--target", shared.TARGET],
            "Dense reducer Charon command differs")

    commands = receipt["commands"]
    require(set(commands) == set(CONTROLS), "Dense reducer control set differs")
    patched_binary = commands["checked"]["command"][0]
    require(Path(patched_binary) == source_root.parent /
                "bulksketch-proof-tools/aeneas-dense-reducer-join/src/_build/default/main.exe",
            "Dense reducer patched binary identity differs")
    for name, (enabled, checked, status) in CONTROLS.items():
        command = commands[name]["command"]
        expected_binaries = {patched_binary}
        if name in ("stock", "portable-xor-stock"):
            expected_binaries = {parent["aeneas_command"][0],
                str(source_root / "verification/lean/tooling/aeneas/src/_build/default/main.exe")}
        flags = [*FLAGS, *(["-checks"] if checked else [])]
        input_path = "extraction/portable-xor/arithmetic.llbc" if name.startswith("portable-xor") else str(EXTRACTION / "arithmetic.llbc")
        require(command[0] in expected_binaries and command[1:-3] == flags and command[-3] == "-dest"
                and Path(command[-2]) == evidence / name and Path(command[-1]) == source_root / "verification/lean" / input_path
                and commands[name]["exit_code"] == status
                and commands[name]["environment"] == (ENVIRONMENT if enabled else {})
                and commands[name]["input_sha256"] == sha(root / input_path),
                "Dense reducer checked command or control differs: " + name)
        output = (root / EXTRACTION / (name + ".log")).read_text()
        if status == 1:
            require("Could not match the contexts" in output and "lines 176:8-178:9" in output,
                    "Dense reducer negative control lost its original failure: " + name)
        else:
            require("Generated the partial file" not in output and "Error" not in output,
                    "Dense reducer successful extraction was partial: " + name)

    exact = {name: sha(root / RAW / name) for name in NAMES}
    require(commands["checked"]["outputs"] == exact and commands["replay"]["outputs"] == exact
            and set(commands["portable-xor"]["outputs"]) == set(NAMES)
            and commands["portable-xor"]["outputs"] == commands["portable-xor-stock"]["outputs"],
            "Dense reducer replay bytes differ")

    llbc = json.loads((root / EXTRACTION / "arithmetic.llbc").read_text())
    translated = llbc["translated"]
    options = translated["options"]
    targets = translated["target_information"]
    require(llbc["has_errors"] is False and options["start_from"] == [SELECTOR]
            and options["opaque"] == [] and options["dest_file"] == capture[4].split("=", 1)[1]
            and len(targets) == 1 and targets[0]["key"] == shared.TARGET
            and targets[0]["value"]["target_pointer_size"] == 8, "Dense reducer LLBC scope differs")
    spans = {}
    for f in translated["fun_decls"]:
        if f:
            meta = f["item_meta"]
            name = meta["name"][-1].get("Ident", [None])[0]
            if name in ("prepare_square_table", "times_x_mod"):
                require(name not in spans and "Structured" in f["body"], "Dense reducer original body missing")
                span = meta["span"]["Untagged"]["data"]
                source = translated["files"][span["file_id"]]
                require(source["name"] == {"Local": SOURCE}
                        and source["contents"].encode() == (root.parents[1] / SOURCE).read_bytes()
                        and sha(root.parents[1] / SOURCE) == SOURCE_SHA256, "original Dense reducer source differs")
                spans[name] = (span["beg"]["line"], span["beg"]["col"], span["end"]["line"], span["end"]["col"])
    require(spans == {"prepare_square_table": (167, 4, 186, 5), "times_x_mod": (234, 0, 240, 1)},
            "Dense reducer original declaration spans differ")

    types = declarations(root / RAW / "Types.lean")
    shared_types = {
        "bridge/Arithmetic/Types.lean": {"types.RawProduct", "types.FieldId", "field.sealed.Sealed", "field.BinaryField"},
        "bridge/Arithmetic/SliceKernelTypes.lean": {"backend.contract.Arithmetic", "backend.contract.BulkKernels"},
        "bridge/Arithmetic/TimesXModRuntime.lean": {"core.ops.range.Bound", "core.ops.range.RangeBounds"},
    }
    require(set(types) == set().union(*shared_types.values()), "Dense reducer shared type set differs")
    for path, names in shared_types.items():
        current = (root / path).read_text()
        require(all(types[name] in current for name in names), "Dense reducer shared type differs: " + path)
    functions = declarations(root / RAW / "Funs.lean")
    shift = declarations(root / "bridge/Arithmetic/TimesXModGenerated.lean")
    require(all(functions[name] == shift.get(name) for name in (SHIFT, RANGE)),
            "Dense reducer modular shift or range dictionary differs")
    expected = HEADER + "\n\n".join(functions[name] for name in FUNCTIONS) + "\n\nend bulksketch\n"
    require((root / ACTIVE).read_text() == expected, "compiled Dense reducer table projection differs")
    require(sha(root / RUNTIME) == receipt["runtime_sha256"], "Dense reducer scoped runtime differs")
    permitted = {"propext", "Classical.choice", "Quot.sound"}
    axioms = re.findall(r"depends on axioms: \[([^\]]*)\]", (root / EXTRACTION / "axioms.log").read_text())
    require(len(axioms) == 3 and all({part.strip() for part in row.split(",")} <= permitted for row in axioms),
            "Dense reducer table axioms differ")
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
