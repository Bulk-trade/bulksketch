#!/usr/bin/env python3
"""Check the original Newton guard projection and checked translator evidence."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/deg34-guard")
RAW = DIRECTORY / "Arithmetic"
ACTIVE = Path("bridge/Arithmetic/NewtonGuardGenerated.lean")
SOURCE = Path("src/decode/deg34.rs")
SOURCE_SHA = "50e92cc158d33b58361cf95719d4f13e01295802a15e1dab7622fab5ce050015"
SOURCE_COMMIT = "0a5bda53f6b07fcae8acd870e2d0c4a246d207e6"
CHARON_COMMIT = "7b462d9159db2ed3015162352183906a30bfafc6"
AENEAS_COMMIT = "ab34bd28458a08c150b7cbf1873e59af74588138"
SELECTOR = "bulksketch::decode::deg34::guard"
VARIANT = "checked-fixedpoint-nested-scalar-slice-retry-v1"
BASE_VARIANT = "checked-fixedpoint-scalar-array-loan-retry-v1"
PATCH = DIRECTORY / "translator/checked-nested-slice-loan-retry.patch"
PATCH_SHA = "7c8426703fb5220a89039735f8f92677e14b7b93efa344851deaa5232bbf6fae"
DELTA = DIRECTORY / "translator/nested-slice-loan-retry-delta.patch"
DELTA_SHA = "b5af23f0e681407135f8b289fc861a8e494cd8d5a110495434d0e3d2e5e3fc0e"
DELTA_SOURCE = "src/interp/InterpMatchCtxs.ml"
MODIFIED_SOURCES = ["src/interp/" + filename for filename in
                    ("InterpJoin.ml", "InterpJoin.mli", "InterpMatchCtxs.ml", "InterpMatchCtxs.mli")]
GENERATED = ("Funs.lean", "Types.lean", "FunsExternal_Template.lean")
ARTIFACTS = {str(DIRECTORY / path) for path in (
    "arithmetic.llbc", "charon.log", "aeneas.log", "pinned.log", "unchecked.log",
    "translator/checked-nested-slice-loan-retry.patch", "translator/nested-slice-loan-retry-delta.patch",
    "translator/controls.log", "translator/guards/nested_slice_loan_controls.ml", "translator/guards/dune",
    "translator/quartic-control.log", "translator/normalize-control.log")}
ARTIFACTS.update(str(RAW / name) for name in GENERATED)
NAMES = ["decode.deg34.guard_loop" + str(branch) + suffix for branch in range(2)
         for suffix in ("_loop0_loop0.body", "_loop0_loop0", "_loop0.body", "_loop0", ".body", "")]
NAMES.append("decode.deg34.guard")
TYPES = ["types.RawProduct", "types.FieldId", "field.sealed.Sealed", "field.BinaryField",
         "backend.contract.Arithmetic", "backend.contract.BulkKernels"]
SHARED_TYPES = ("bridge/Arithmetic/Types.lean", "bridge/Arithmetic/SliceKernelTypes.lean")
CONTROLS = ("end-left-shared", "end-right-shared", "unchecked", "original-mode", "different-parent",
            "no-mutable-parent", "different-element-type", "non-symbolic-payload", "mismatched-payload-type",
            "mismatched-symbolic-type")
HEADER = """-- Exact original-source declaration projection. Imports are adapted only.
module
public import Arithmetic.SliceKernelTypes
public import Arithmetic.TrailingZeros
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

"""


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def blocks(path):
    body = path.read_text().split("namespace bulksketch\n", 1)[1].rsplit("end bulksketch", 1)[0]
    result = {}
    for block in re.findall(r"(?ms)^/--.*?(?=^/--|\Z)", body):
        names = re.findall(r"(?m)^(?:def|impl_def|structure|inductive|abbrev)\s+(\S+)", block)
        require(len(names) == 1 and names[0] not in result, "invalid Newton guard declaration block: " + str(path))
        result[names[0]] = block
    return result


def check_translator(root, receipt):
    require(receipt["candidate_variant"] == VARIANT and receipt["extension_of"] == BASE_VARIANT
            and receipt["delta_modified_source"] == DELTA_SOURCE, "Newton guard translator identity differs")
    for path, expected, key, sources in (
            (PATCH, PATCH_SHA, "full_patch_sha256", MODIFIED_SOURCES),
            (DELTA, DELTA_SHA, "delta_patch_sha256", [DELTA_SOURCE])):
        require(sha(root / path) == expected == receipt[key]
                and re.findall(r"(?m)^--- a/(\S+)\n\+\+\+ b/(\S+)$", (root / path).read_text()) ==
                [(source, source) for source in sources], "Newton guard translator patch differs")
    commands = {entry["name"]: entry for entry in receipt["checks"]}
    expected_codes = {"charon": 0, "build": 0, "Arithmetic": 1, "slice-retry": 0, "replay": 0,
                      "pinned": 1, "unchecked": 1, "quartic-control": 0, "normalize-control": 0, "guard-controls": 0}
    require(len(commands) == len(receipt["checks"]) and
            {name: item["exit_code"] for name, item in commands.items()} == expected_codes,
            "Newton guard translator command matrix differs")
    original_llbc = sha(root / DIRECTORY / "arithmetic.llbc")
    for name, log in (("replay", "aeneas.log"), ("pinned", "pinned.log"), ("unchecked", "unchecked.log"),
                      ("quartic-control", "translator/quartic-control.log"),
                      ("normalize-control", "translator/normalize-control.log")):
        entry = commands[name]
        flags = set(entry["command"])
        require(sha(root / DIRECTORY / log) == entry["log_sha256"] and "-sequential" in flags
                and ("-checks" in flags) == (name != "unchecked"), "Newton guard translator log or flags differ")
        if name in ("replay", "pinned", "unchecked"):
            require(entry["input_sha256"] == original_llbc, "Newton guard replay input differs")
        if name in ("pinned", "unchecked"):
            raw_log = (root / DIRECTORY / log).read_text()
            require("src/decode/deg34.rs', lines 49:8-57:9" in raw_log and "Unimplemented" in raw_log,
                    "Newton guard rejection changed")
    require(tuple(receipt["guard_controls"]) == CONTROLS and
            (root / DIRECTORY / "translator/controls.log").read_text().splitlines() == ["PASS " + name for name in CONTROLS]
            and receipt["replayed_files_byte_identical"] == 3
            and receipt["quartic_control_files_byte_identical"] == 3
            and receipt["normalization_control_files_byte_identical"] == 3,
            "Newton guard translator controls differ")
    for key, directory in (("quartic", "quartic"), ("normalize", "deg34-normalize")):
        source = root / "extraction" / directory
        require(sha(source / "arithmetic.llbc") == commands[key + "-control"]["input_sha256"]
                and {name: sha(source / "Arithmetic" / name) for name in GENERATED} == receipt["control_output_hashes"][key],
                "Newton guard translator control outputs differ")


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    require(receipt["status"] == "checked_original_closure_extracted" and receipt["selected_root"] == SELECTOR
            and receipt["source_commit"] == SOURCE_COMMIT and receipt["charon_commit"] == CHARON_COMMIT
            and receipt["aeneas_commit"] == AENEAS_COMMIT and receipt["source_sha256"] == SOURCE_SHA
            and receipt["native_source_edited"] is False and receipt["llbc_has_errors"] is False
            and receipt["transparent_application_bodies"] is True, "invalid Newton guard extraction receipt")
    require(set(receipt["files_sha256"]) == ARTIFACTS, "incomplete Newton guard artifact set")
    for path, expected in receipt["files_sha256"].items():
        require(sha(root / path) == expected, "Newton guard artifact differs: " + path)
    check_translator(root, receipt)
    require(sha(root.parents[1] / SOURCE) == SOURCE_SHA, "frozen Newton guard Rust source differs")
    llbc = json.loads((root / DIRECTORY / "arithmetic.llbc").read_text())
    translated = llbc["translated"]
    require(llbc["has_errors"] is False and translated["options"]["start_from"] == [SELECTOR]
            and translated["options"]["opaque"] == [], "Newton guard LLBC closure differs")
    target = translated["target_information"]
    require(len(target) == 1 and target[0]["key"] == "x86_64-apple-darwin"
            and target[0]["value"]["target_pointer_size"] == 8, "unexpected Newton guard target")
    path = [{"Ident": [part, 0]} for part in SELECTOR.split("::")]
    matching = [fn for fn in translated["fun_decls"] if fn and fn["item_meta"]["name"] == path]
    require(len(matching) == 1 and "Structured" in matching[0]["body"], "Newton guard LLBC body missing")
    span = matching[0]["item_meta"]["span"]["Untagged"]["data"]
    source = translated["files"][span["file_id"]]
    require(span["beg"] == {"line": 10, "col": 0} and span["end"] == {"line": 63, "col": 1}
            and source["name"] == {"Local": str(SOURCE)}
            and hashlib.sha256(source["contents"].encode()).hexdigest() == SOURCE_SHA,
            "Newton guard LLBC source span or contents differ")
    shared = [(root / name).read_text() for name in SHARED_TYPES]
    types = blocks(root / RAW / "Types.lean")
    require(list(types) == TYPES and all(any(block.strip() in text for text in shared) for block in types.values()),
            "Newton guard shared types differ")
    template = (root / RAW / "FunsExternal_Template.lean").read_text()
    require(re.findall(r"(?m)^axiom\s+(\S+)", template) == ["core.num.Usize.trailing_zeros", "core.slice.raw.from_ref"],
            "Newton guard external declaration set differs")
    functions = blocks(root / RAW / "Funs.lean")
    require([name for name in functions if name.startswith("decode.deg34.guard")] == NAMES,
            "Newton guard declaration set differs")
    require({name: hashlib.sha256(functions[name].strip().encode()).hexdigest() for name in NAMES} ==
            receipt["generated_guard_declarations_sha256"], "Newton guard declaration hashes differ")
    projected = HEADER + "".join(functions[name] for name in NAMES) + "end bulksketch\n"
    require((root / ACTIVE).read_text() == projected, "compiled Newton guard projection differs")
    return {
        "raw_generated_file": str(RAW / "Funs.lean"), "raw_file_sha256": sha(root / RAW / "Funs.lean"),
        "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
        "source_declarations_retained_verbatim": len(NAMES),
        "shared_types_and_function_dictionary_declarations_checked": True,
        "generated_declarations": ["bulksketch." + name for name in NAMES],
        "translator_variant": VARIANT, "native_source_edited": False,
    }


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
