#!/usr/bin/env python3
"""Verify the frozen original completed_result and its scoped checked translation."""
from hashlib import sha256
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/completed-result")
RAW = DIRECTORY / "Arithmetic"
ACTIVE = Path("bridge/Arithmetic/CompletedResultGenerated.lean")
COMPAT = Path("extraction/execution-verify")


def import_at(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


setup = import_at("completed_root_setup", ROOT / "extraction/root-setup/project.py")
controls = import_at("completed_scope_controls", ROOT / DIRECTORY / "scope_controls.py")
require, sha, declarations = setup.require, setup.sha, setup.declarations

VARIANT = "checked-completed-result-frozen-shared-v1"
PATCH = DIRECTORY / "checked-completed-result-frozen-shared.patch"
PATCH_HASH = "072f57a70e79f9fa4ec42feabeb5cbfdae3c757b0af09ade5a4079a642fb6b60"
CAPTURE = controls.CAPTURE
RECAPTURE = "10cb3d04e8ed82c6bc056f230ef98755d2fac607b83269713b7c8c5bf0f483ee"
PATCHED_BINARY = "49ca05c2307e682cdb112c6b9a8fccd3784c774b621fe44355fd22755547a3f6"
BASE_SOURCES = {"src/interp/InterpJoin.ml": "57c5478aae42f8a354755424b67f67f37dc8bd233d653c97de0dcbbea5dd6229"}
MODIFIED_SOURCES = {"src/interp/InterpJoin.ml": "7b7b982db6c128a0950c969218813bf10b86a405d6c92530814d5dfdcb3e34b4"}
OUTPUT_HASHES = {
    "Funs.lean": "ed2942f11ed9521dcb98a3252b66bff8863de6a60d94bd9648a65462da502469",
    "Types.lean": "2d71cb04b7390ef2f3b869192ac4d6ac8a0717d11efd87ad81155052fa07020e",
    "FunsExternal_Template.lean": "6dda48e52e9081ad1680028efb94fbb0f0f7ca7fd85344e4d9ba34c68b90d829",
}
SOURCE_HASHES = {
    "src/lib.rs": "5174f3741a1c1b0bbdfddfac894adb8d96de06896dce8960bad76fe2056fe124",
    "src/decode/stages.rs": "93825fcb5054e98e9af060a81da72d4770c29354d79822ccfc949cc55f6e9b23",
    "src/decode/mod.rs": "4d1f559feaa82a6f89e4ddd533fb7fa526d5637386364385020888c25e6026b4",
    "src/field/mod.rs": "035dc6193ebb50b324527525c0ee47cbe06ca325db16aa5f8ee55b0e79baa723",
    "src/backend/mod.rs": "b4883e5070592cd5db4c9450fbc14e7dc9c07ec457029a54917295a24a94fb72",
    "src/backend/contract.rs": "4d05ce564edc408ba04f5a907b159ad91018ba8cfd93126e17913ed49f7e3d59",
    "src/types.rs": "5702a8552c1158cf69f2155d2484f246f87475dc6bef3ea734be52348acd940d",
    "src/decode/row.rs": "bf5ae89114d3bab811f1e0ca3b370cd916803bddd178471b3167e81b432df7bc",
    "src/decode/roots.rs": "4697d5874fd1eb03c0210371fdac83a8dc7171de2724da046613f59c879f4fb6",
    "src/decode/degree_probe.rs": "60d72b0aa11f311c4359bfe94f0d6fede00723602b3251492cbdb10ee51752ed",
    "src/decode/scratch.rs": "97016cadabf021829b567ff1472a9f11136f54059d78e457d58896cc318e50f6",
}
TYPES = {
    "bridge/Arithmetic/Types.lean": ("types.RawProduct", "types.FieldId", "field.sealed.Sealed", "field.BinaryField"),
    "bridge/Arithmetic/SliceKernelTypes.lean": ("backend.contract.Arithmetic", "backend.contract.BulkKernels"),
    "bridge/Workmeter/Types.lean": ("types.DecodeError",),
    "bridge/Arithmetic/ReconstructionTypes.lean": (
        "core.marker.PhantomData", "types.Stage", "decode.degree_probe.DegreeProbe", "decode.roots.Roots",
        "types.DecodeFailure", "decode.row.RowBudget", "decode.scratch.FactorFrame", "decode.scratch.SplitterBasis",
        "decode.scratch.RowWorkspace", "decode.stages.State", "decode.stages.Execution",
    ),
}
NAME = "decode.stages.Execution.completed_result"
ROW_RESULT = "decode.row.RowResult"
SELECTOR = "bulksketch::decode::stages::_::completed_result"
CONTROLS = {"stock": 1, "flag-off": 1, "unchecked": 1, "checked": 0,
            "wrong-site": 1, "wrong-workspace": 1, "execution-verify": 0}
MUTATIONS = {
    "wrong-site": "4af1d4132e6b37adfc7a2056737db152b185d1d95f9ad821ea698bfa337b1af1",
    "wrong-workspace": "15f7a20b53ff69e497f5ecad53ff4ad1ad724b6babe3c1b538e21128517e44ff",
}
ARTIFACTS = {str(RAW / name) for name in OUTPUT_HASHES} | {str(PATCH)}
ARTIFACTS |= {str(DIRECTORY / name) for name in (
    "arithmetic.llbc", "charon.log", "fresh-build.log", "scope_controls.py", "strict-joins.log",
)}
ARTIFACTS |= {str(DIRECTORY / (name + ".log")) for name in CONTROLS}
HEADER = """-- Original checked completed-result projection preserving the shared roots prefix.
import Arithmetic.ReconstructionTypes

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false

namespace bulksketch

"""


def sha_bytes(data):
    return sha256(data).hexdigest()


def output_hashes(root, directory):
    return {name: sha(root / directory / name) for name in OUTPUT_HASHES}


def place_path(place):
    local, path = place["kind"], []
    while "Projection" in local:
        parent, projection = local["Projection"]
        path.append(projection)
        local = parent["kind"]
    return local["Local"], list(reversed(path))


def check_llbc(root, data):
    require(sha_bytes(data) == CAPTURE, "original completed_result capture differs")
    llbc = json.loads(data)
    crate = llbc["translated"]
    options, targets = crate["options"], crate["target_information"]
    require(llbc["has_errors"] is False and options["start_from"] == [SELECTOR] and
            options["include"] == [SELECTOR] and options["opaque"] == [] and
            len(targets) == 1 and targets[0]["key"] == setup.TARGET and
            targets[0]["value"]["target_pointer_size"] == 8, "completed_result capture scope or target differs")
    for path, digest in SOURCE_HASHES.items():
        require(sha(root.parents[1] / path) == digest, "pinned completion source differs: " + path)
        embedded = [entry["contents"] for entry in crate["files"] if entry and entry["name"] == {"Local": path}]
        require(len(embedded) == 1 and sha_bytes(embedded[0].encode()) == digest,
                "embedded completion source differs: " + path)
    function, = [fn for fn in crate["fun_decls"] if fn
                 and fn["item_meta"]["name"][-1].get("Ident") == ["completed_result", 0]]
    span = function["item_meta"]["span"]["Untagged"]
    location = span["data"]
    require(crate["files"][location["file_id"]]["name"] == {"Local": "src/decode/stages.rs"} and
            location["beg"] == {"line": 142, "col": 4} and location["end"] == {"line": 157, "col": 5} and
            span["generated_from_span"] is None and "Structured" in function["body"],
            "original completed_result source span or body differs")
    sig = function["signature"]
    self_ref, workspace_ref = [item["Value"][1]["Ref"] for item in sig["inputs"]]
    inner_workspace = workspace_ref[1]["Value"][1]["Adt"]
    row_result = sig["output"]["Value"][1]["Adt"]["generics"]["types"][0]["Value"][1]["Adt"]
    require(self_ref[0] == {"Var": {"Free": 1}} and self_ref[2] == "Shared" and
            workspace_ref[0] == {"Var": {"Free": 0}} and workspace_ref[2] == "Shared" and
            inner_workspace["generics"]["regions"] == [{"Var": {"Free": 2}}] and
            row_result["generics"]["regions"] == [{"Var": {"Free": 0}}],
            "completed_result shared roots return lifetime differs")
    statements = {node["id"]: node["kind"] for node in controls.walk(function["body"])
                  if set(node) == {"span", "id", "kind", "comments_before"}}
    require({i for i, kind in statements.items() if isinstance(kind, dict) and "Switch" in kind} ==
            {74, 105, 135}, "completed_result switch set differs")
    for borrow, count, read, result in ((50, 53, 62, 67), (81, 84, 93, 98)):
        ref = statements[borrow]["Assign"][1]["Ref"]
        count_place = statements[count]["Assign"][1]["Use"][0]["Copy"]
        call = statements[read]["Call"]
        tag, fields = statements[result]["Assign"][1]["Aggregate"]
        require(ref["kind"] == "Shared" and
                place_path(ref["place"]) == (2, ["Deref", {"Field": [None, 6]}, "Deref"]) and
                place_path(ref["ptr_metadata"]["Copy"]) == (2, ["Deref", {"Field": [None, 6]}, "PtrMetadata"]) and
                place_path(count_place) == (1, ["Deref", {"Field": [None, 4]}, {"Field": [None, 7]}]) and
                call["call"]["func"]["Regular"]["kind"] == {"Fun": 4} and
                [place_path(arg["Move"]) for arg in call["call"]["args"]] == [(19, []), (20, [])] and
                tag["Adt"][0]["id"] == row_result["id"] and tag["Adt"][1] == 1 and
                [place_path(arg["Move"]) for arg in fields] == [(16, [])],
                "completed_result original shared roots read differs")
    return Path(options["dest_file"])


def check_receipt(root, receipt, original, data):
    require(receipt["variant_id"] == VARIANT and receipt["source_commit"] == setup.SOURCE and
            receipt["aeneas_commit"] == setup.AENEAS and receipt["charon_commit"] == setup.CHARON and
            receipt["target"] == setup.TARGET and receipt["rust_toolchain"] == "nightly-2026-09-17" and
            receipt["native_source_edited"] is False and receipt["native_llbc_edited"] is False and
            receipt["source_sha256"] == SOURCE_HASHES and receipt["capture_sha256"] == CAPTURE and
            receipt["variant_patch"] == str(PATCH) and receipt["variant_patch_sha256"] == PATCH_HASH and
            receipt["base_sources"] == BASE_SOURCES and receipt["modified_sources"] == MODIFIED_SOURCES and
            receipt["patched_binary_sha256"] == PATCHED_BINARY and set(receipt["files_sha256"]) == ARTIFACTS,
            "invalid completed_result translator receipt")
    for path, expected in receipt["files_sha256"].items():
        require(sha(root / path) == expected, "completed_result artifact differs: " + path)
    require(sha(root / PATCH) == PATCH_HASH, "completed_result translator patch differs")
    parent = json.loads((root / "extraction/root-setup/receipt.json").read_text())
    manifest = next(word for word in parent["charon_command"] if word.startswith("--manifest-path="))
    native_repo = Path(manifest.removeprefix("--manifest-path=")).parent
    evidence = native_repo.parent / "bulksketch-proof-evidence-20261109-native-driver/completed-result"
    require(original == evidence / "arithmetic.llbc", "completed_result historical capture path differs")
    rebuilt = evidence / "fresh-tool/src"
    patched = rebuilt / "_build/default/main.exe"
    recapture = original.with_name("recaptured.llbc")
    command = [parent["charon_command"][0], "cargo", "--preset=aeneas", "--sysroot=default",
               "--dest-file=" + str(recapture), "--start-from=" + SELECTOR, "--include=" + SELECTOR,
               "--", manifest, "-p", "bulksketch", "--lib", "--locked", "--offline", "--target", setup.TARGET]
    require(receipt["charon_recapture"] == {
        "command": command, "exit_code": 0, "binary_sha256": setup.BINARY_SHA256["charon"],
        "original_sha256": CAPTURE, "recapture_sha256": RECAPTURE,
        "normalized_fields": ["translated.options.dest_file"], "log_sha256": sha(root / DIRECTORY / "charon.log"),
    } and sha_bytes(data.replace(str(original).encode(), str(recapture).encode(), 1)) == RECAPTURE,
        "completed_result stock Charon recapture differs beyond the destination")
    require(receipt["fresh_build"] == {
        "command": ["dune", "build", "--root", str(rebuilt), "-j", "2", "./main.exe"],
        "exit_code": 0, "source_files_byte_identical": 108, "modified_source_sha256": MODIFIED_SOURCES,
        "log_sha256": sha(root / DIRECTORY / "fresh-build.log"),
    }, "completed_result checked fresh build differs")

    require(receipt["strict_join_replay"] == {
        "command": [str(patched), "-backend", "lean", "-checks", "-strict-joins", "-sequential",
                    "-no-progress-bar", "-print-error-emitters", "-split-files", "-dest",
                    str(evidence / "strict-joins"), str(original)],
        "environment": {controls.FLAG: "1"}, "exit_code": 0, "binary_sha256": PATCHED_BINARY,
        "input_sha256": CAPTURE, "log_sha256": sha(root / DIRECTORY / "strict-joins.log"),
        "outputs": OUTPUT_HASHES,
    }, "completed_result strict-join replay differs")

    rows = receipt["controls"]
    require(set(rows) == set(CONTROLS) and receipt["replay"] == rows["checked"],
            "incomplete completed_result controls or missing checked replay")
    control_dir = evidence / "fresh-controls"
    for name, status in CONTROLS.items():
        log = root / DIRECTORY / (name + ".log")
        if status:
            diagnostic = log.read_text()
            compiler = "InterpBorrows.ml, line 1542" if name == "unchecked" else "Invariants.ml, line 212"
            span = "142:4-157:5" if name == "unchecked" else "146:9-157:5" if name == "wrong-site" else "146:8-157:5"
            require("Could not translate the body" in diagnostic and
                    f"Source: 'src/decode/stages.rs', lines {span}" in diagnostic and
                    f"Compiler source: interp/{compiler}" in diagnostic, "completion control rejection moved: " + name)
        tool = parent["aeneas_command"][0] if name == "stock" else str(patched)
        if name == "execution-verify":
            source = native_repo / "verification/lean" / COMPAT / "arithmetic.llbc"
            input_digest = sha(root / COMPAT / "arithmetic.llbc")
            outputs = output_hashes(root, COMPAT / "Arithmetic")
        elif name in MUTATIONS:
            source = control_dir / (name + ".llbc")
            input_digest, outputs = sha_bytes(controls.mutation(data, name)), {}
            require(input_digest == MUTATIONS[name], "completed_result synthetic control differs: " + name)
        else:
            source = original
            input_digest, outputs = CAPTURE, {} if status else OUTPUT_HASHES
        require(rows[name] == {
            "command": [tool, *controls.FLAGS, *(["-checks"] if name != "unchecked" else []),
                        "-dest", str(control_dir / name), str(source)],
            "environment": {} if name in ("stock", "flag-off") else {controls.FLAG: "1"}, "exit_code": status,
            "binary_sha256": setup.BINARY_SHA256["aeneas"] if name == "stock" else PATCHED_BINARY,
            "input_sha256": input_digest, "log_sha256": sha(log), "outputs": outputs,
        }, "completed_result control differs: " + name)


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    data = (root / DIRECTORY / "arithmetic.llbc").read_bytes()
    original = check_llbc(root, data)
    check_receipt(root, receipt, original, data)
    require(output_hashes(root, RAW) == OUTPUT_HASHES, "frozen completed_result Lean output differs")
    types = declarations(root / RAW / "Types.lean")
    require(set(types) == {ROW_RESULT} | {name for names in TYPES.values() for name in names},
            "completed_result generated type set differs")
    for path, names in TYPES.items():
        shared = declarations(root / path)
        require(all(types[name] == shared[name] for name in names), "completed_result shared type differs: " + path)
    source = declarations(root / RAW / "Funs.lean")
    projected = HEADER + "\n\n".join((types[ROW_RESULT], source[NAME])) + "\n\nend bulksketch\n"
    require("sorry" not in source[NAME] and (root / ACTIVE).read_text() == projected,
            "compiled completed_result projection differs")
    return {
        "raw_generated_file": str(RAW / "Funs.lean"), "raw_file_sha256": OUTPUT_HASHES["Funs.lean"],
        "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
        "source_declarations_retained_verbatim": 2,
        "shared_types_and_function_dictionary_declarations_checked": True,
        "generated_declarations": ["bulksketch." + ROW_RESULT, "bulksketch." + NAME],
        "native_source_edited": False, "translator_variant": VARIANT,
    }


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
