#!/usr/bin/env python3
"""Verify the frozen finish source, exact scoped prepass and compiled projection."""
from hashlib import sha256
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/native-finish")
RAW = DIRECTORY / "Arithmetic"
ACTIVE = Path("bridge/Arithmetic/FinishGenerated.lean")
COMPAT = Path("extraction/native-driver/run-next")


def import_at(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


completed = import_at("finish_completed_project", ROOT / "extraction/completed-result/project.py")
verify = import_at("finish_execution_verify", ROOT / "extraction/execution-verify/project.py")
controls = import_at("finish_controls", ROOT / DIRECTORY / "finish_controls.py")
setup = completed.setup
require, sha, declarations = verify.require, verify.sha, verify.declarations
sha_bytes = completed.sha_bytes

VARIANT = "checked-finish-return-boundary-v1"
PATCH = DIRECTORY / "checked-finish-return-boundary.patch"
PATCH_HASH = "8dff3576cb08a725098b0605e85802752054e98aad35d30c14dd87270f3b32ae"
CAPTURE = controls.CAPTURE
RECAPTURE = "e46e241e62d82a2f2d22f8c8d2d8a1e9f411dd48a30900c52935739f9ff6b30f"
PATCHED_BINARY = "bf759160c6c7ba10937ab75ad9e2b0bf83a99760615d348a3639e082bacecec3"
BASE_SOURCES = {"src/PrePasses.ml": "ae752eeef3227b7566611fa7d3ace71fd64fbf24c088bc7ce16699a243772165"}
MODIFIED_SOURCES = {"src/PrePasses.ml": "0241f4262a1f3e8c2c2a47b69ffa6c105cb980f9658471ca751b79104b11162b"}
OUTPUT_HASHES = {
    "Funs.lean": "c64f8a5741fb3879c03eeaca9b6aa8321f529fa9796ace98edd464d1986a0e60",
    "FunsExternal_Template.lean": "1a9a5cc4c36f3314662b4f1612ad3a91bb53bcb2ddbe13deb1bb39c113cdd32c",
    "Types.lean": "86fd0f48a0fd8b1e1f3b231bedafc7b956fec0748cbc2b76c1a5ed24b7d643ea",
}
SOURCE_HASHES = completed.SOURCE_HASHES
TYPES = {**completed.TYPES,
         "bridge/Arithmetic/CompletedResultGenerated.lean": ("decode.row.RowResult",),
         "bridge/Workmeter/Types.lean": ("types.WorkUnits", "types.WorkMeter", "types.DecodeError"),
         "bridge/Arithmetic/ExecutionDriverGenerated.lean": ("decode.row.RowProgress",),
         "bridge/Arithmetic/ReconstructionTypes.lean":
             (*completed.TYPES["bridge/Arithmetic/ReconstructionTypes.lean"],
              "decode.row.RowInput")}
TRAIT = "{impl bulksketch::decode::row::RowExecution for bulksketch::decode::stages::Execution}"
SELECTOR = TRAIT + "::finish"
OPAQUE = ["bulksketch::decode::stages::_::completed_result", "bulksketch::decode::stages::_::execute",
          TRAIT + "::run_next", TRAIT + "::next_stage"]
IMPL = "decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution"
NAMES = tuple(IMPL + "." + name for name in ("finish_loop.body", "finish_loop", "finish"))
CALLEES = {
    "decode.stages.Execution.completed_result": "bridge/Arithmetic/CompletedResultGenerated.lean",
    IMPL + ".run_next": "bridge/Arithmetic/ExecutionDriverGenerated.lean",
    IMPL + ".next_stage": "bridge/Arithmetic/ExecutionDriverGenerated.lean",
}
CONTROLS = {"stock": 1, "flag-off": 1, "unchecked": 1, "checked": 0, "strict-joins": 0,
            "wrong-site": 1, "wrong-residual": 1, "run-next": 0}
MUTATIONS = {"wrong-site": "49c590b7f082ad534f21df1e62cf73e4c364468d5bf49362ec2857ae0853be3c", "wrong-residual": "d95406197fd194a01d8a55640758323b74dc35a2dfcd19ff3c4ace0e80787a00"}
ARTIFACTS = {str(RAW / name) for name in OUTPUT_HASHES} | {str(PATCH)}
ARTIFACTS |= {str(DIRECTORY / name) for name in (
    "arithmetic.llbc", "charon.log", "fresh-build.log", "finish_controls.py",
)}
ARTIFACTS |= {str(DIRECTORY / (name + ".log")) for name in CONTROLS}
HEADER = """-- Checked original finish projection with a scoped shared-return boundary.
import Arithmetic.ExecutionDriverGenerated
import Arithmetic.CompletedResultGenerated

open Aeneas Aeneas.Std Result ControlFlow Error
open Aeneas.Std.ExecutionDriverRuntime
set_option linter.unusedVariables false
set_option maxRecDepth 4096

namespace bulksketch

variable (calls : RootRunRuntime.OtherCallees) (division : DenseDivisionRuntime.DivRem)
variable (canonicalizeModel : Canonicalize)

"""
MARKER = "/-- [bulksketch::decode::stages::{impl bulksketch::decode::row::RowExecution for bulksketch::decode::stages::Execution<F, K>}::finish]"


def notation(name):
    return f'local notation "{IMPL}.{name}" => ({IMPL}.{name} calls division canonicalizeModel)\n\n'


def project(raw):
    _, marker, suffix = raw.partition(MARKER)
    require(marker, "finish source marker is missing")
    selected = marker + suffix
    for name, anchor in (("finish_loop.body", ": loop 0:"), ("finish_loop", ":\n    Source:")):
        pos = selected.index(MARKER + anchor)
        selected = selected[:pos] + notation(name) + selected[pos:]
    return HEADER + notation("run_next") + selected


def output_hashes(root, directory):
    return {name: sha(root / directory / name) for name in OUTPUT_HASHES}


def check_llbc(root, data):
    require(sha_bytes(data) == CAPTURE, "original finish capture differs")
    llbc = json.loads(data)
    crate = llbc["translated"]
    opts, targets = crate["options"], crate["target_information"]
    require(llbc["has_errors"] is False and opts["start_from"] == [SELECTOR] and opts["include"] == [SELECTOR]
            and opts["opaque"] == OPAQUE and len(targets) == 1 and targets[0]["key"] == setup.TARGET
            and targets[0]["value"]["target_pointer_size"] == 8, "finish capture scope or target differs")
    for path, digest in SOURCE_HASHES.items():
        require(sha(root.parents[1] / path) == digest, "pinned finish source differs: " + path)
        embedded = [entry["contents"] for entry in crate["files"] if entry and entry["name"] == {"Local": path}]
        require(len(embedded) == 1 and sha_bytes(embedded[0].encode()) == digest,
                "embedded finish source differs: " + path)
    function = controls.select(llbc)
    span = function["item_meta"]["span"]["Untagged"]
    loc = span["data"]
    require(crate["files"][loc["file_id"]]["name"] == {"Local": "src/decode/stages.rs"} and
            loc["beg"] == {"line": 442, "col": 4} and loc["end"] == {"line": 452, "col": 5} and
            span["generated_from_span"] is None and "Structured" in function["body"],
            "original finish source span or body differs")
    sig = function["signature"]
    workspace = sig["inputs"][2]["Value"][1]["Ref"]
    row_result = sig["output"]["Value"][1]["Adt"]["generics"]["types"][0]["Value"][1]["Adt"]
    require(workspace[0] == {"Var": {"Free": 0}} and workspace[2] == "Mut" and
            row_result["generics"]["regions"] == [{"Var": {"Free": 0}}],
            "finish original returned shared result lifetime differs")
    statements = function["body"]["Structured"]["body"]["statements"]
    require([st["id"] for st in statements] == [0,103,104,105,109,111,112,113,114,122,123,124,127,128,129,130,131],
            "finish original loop and suffix order differs")
    loop = statements[1]["kind"]["Loop"]["statements"]
    by_id = {st["id"]: st for st in loop}
    normal = by_id[29]["kind"]["Switch"]["branches"][1]["statements"]
    early = by_id[93]["kind"]["Switch"]["branches"][1]["statements"]
    require(len(normal) == 1 and normal[0]["kind"] == {"Break": 0}
            and [st["id"] for st in early] == [66,67,68,69,77,78,79,80,81,82,86,87,88,89,90]
            and early[-1]["kind"] == "Return" and statements[-1]["kind"] == "Return",
            "finish original normal break or early residual return differs")
    for call, name, moves in (
            (by_id[16], "next_stage", [8]), (by_id[50], "run_next", [12,13,14,15]),
            (early[4], "from_residual", [17]), (statements[9], "completed_result", [19,20])):
        original = call["kind"]["Call"]["call"]
        fid = original["func"]["Regular"]["kind"]["Fun"]
        callee, = [entry for entry in crate["fun_decls"] if entry and entry["def_id"] == fid]
        require(callee["item_meta"]["name"][-1].get("Ident") == [name, 0] and
                [arg["Move"]["kind"]["Local"] for arg in original["args"]] == moves,
                "finish original call or input differs: " + name)
        if name in ("next_stage", "run_next", "completed_result"):
            require(callee["body"] == "Opaque", "finish callee must be supplied by the checked original declaration")
    return Path(opts["dest_file"])


def check_receipt(root, receipt, original, data):
    require(receipt["variant_id"] == VARIANT and receipt["source_commit"] == setup.SOURCE and
            receipt["aeneas_commit"] == setup.AENEAS and receipt["charon_commit"] == setup.CHARON and
            receipt["target"] == setup.TARGET and receipt["rust_toolchain"] == "nightly-2026-09-17" and
            receipt["native_source_edited"] is False and receipt["native_llbc_edited"] is False and
            receipt["source_sha256"] == SOURCE_HASHES and receipt["capture_sha256"] == CAPTURE and
            receipt["variant_patch"] == str(PATCH) and receipt["variant_patch_sha256"] == PATCH_HASH and
            receipt["base_sources"] == BASE_SOURCES and receipt["modified_sources"] == MODIFIED_SOURCES and
            receipt["patched_binary_sha256"] == PATCHED_BINARY and set(receipt["files_sha256"]) == ARTIFACTS,
            "invalid finish checked translator receipt")
    for path, expected in receipt["files_sha256"].items():
        require(sha(root / path) == expected, "finish artifact differs: " + path)
    require(sha(root / PATCH) == PATCH_HASH, "finish translator patch differs")
    parent = json.loads((root / "extraction/root-setup/receipt.json").read_text())
    manifest = next(word for word in parent["charon_command"] if word.startswith("--manifest-path="))
    native_repo = Path(manifest.removeprefix("--manifest-path=")).parent
    evidence = native_repo.parent / "bulksketch-proof-evidence-20261109-native-driver/finish-stock"
    require(original == evidence / "arithmetic.llbc", "finish historical capture path differs")
    rebuilt = evidence / "final-finish-tool/src"
    patched = rebuilt / "_build/default/main.exe"
    recapture = original.with_name("recaptured.llbc")
    command = [parent["charon_command"][0], "cargo", "--preset=aeneas", "--sysroot=default",
               "--dest-file=" + str(recapture), "--start-from=" + SELECTOR, "--include=" + SELECTOR,
               *("--opaque=" + name for name in OPAQUE),
               "--", manifest, "-p", "bulksketch", "--lib", "--locked", "--offline", "--target", setup.TARGET]
    require(receipt["charon_recapture"] == {
        "command": command, "exit_code": 0, "binary_sha256": setup.BINARY_SHA256["charon"],
        "original_sha256": CAPTURE, "recapture_sha256": RECAPTURE,
        "normalized_fields": ["translated.options.dest_file"], "log_sha256": sha(root / DIRECTORY / "charon.log"),
    } and sha_bytes(data.replace(str(original).encode(), str(recapture).encode(), 1)) == RECAPTURE,
        "finish stock Charon recapture differs beyond the destination")
    require(receipt["fresh_build"] == {
        "command": ["dune", "build", "--root", str(rebuilt), "-j", "2", "./main.exe"],
        "exit_code": 0, "source_files_byte_identical": 108, "modified_source_sha256": MODIFIED_SOURCES,
        "log_sha256": sha(root / DIRECTORY / "fresh-build.log"),
    }, "finish checked fresh build differs")

    rows = receipt["controls"]
    require(set(rows) == set(CONTROLS) and receipt["replay"] == rows["checked"],
            "incomplete finish controls or missing checked replay")
    control_dir = evidence / "final-controls"
    for name, status in CONTROLS.items():
        log = root / DIRECTORY / (name + ".log")
        if status:
            diagnostic = log.read_text()
            if name == "wrong-residual":
                require("Unexpected original RowExecution::finish return boundary" in diagnostic
                        and "Compiler source: PrePasses.ml" in diagnostic, "finish wrong residual was not rejected by scope")
            else:
                require("Found a case of unsupported nested borrows" in diagnostic and
                        "Source: 'src/decode/stages.rs', lines 448:8-452:5" in diagnostic and
                        "Compiler source: interp/InterpBorrows.ml, line 2060" in diagnostic,
                        "finish control rejection moved: " + name)
        tool = parent["aeneas_command"][0] if name == "stock" else str(patched)
        if name == "run-next":
            source = native_repo / "verification/lean" / COMPAT / "arithmetic.llbc"
            input_digest = sha(root / COMPAT / "arithmetic.llbc")
            outputs = output_hashes(root, COMPAT / "Arithmetic")
        elif name in MUTATIONS:
            source = control_dir / (name + ".llbc")
            input_digest, outputs = sha_bytes(controls.mutation(data, name)), {}
            require(input_digest == MUTATIONS[name], "finish synthetic control differs: " + name)
        else:
            source = original
            input_digest, outputs = CAPTURE, {} if status else OUTPUT_HASHES
        require(rows[name] == {
            "command": [tool, *controls.FLAGS, *(["-checks"] if name != "unchecked" else []),
                        *(["-strict-joins"] if name == "strict-joins" else []),
                        "-dest", str(control_dir / name), str(source)],
            "environment": {} if name in ("stock", "flag-off") else {controls.FLAG: "1"}, "exit_code": status,
            "binary_sha256": setup.BINARY_SHA256["aeneas"] if name == "stock" else PATCHED_BINARY,
            "input_sha256": input_digest, "log_sha256": sha(log), "outputs": outputs,
        }, "finish control differs: " + name)


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    data = (root / DIRECTORY / "arithmetic.llbc").read_bytes()
    original = check_llbc(root, data)
    check_receipt(root, receipt, original, data)
    require(output_hashes(root, RAW) == OUTPUT_HASHES, "frozen finish Lean output differs")
    types = declarations(root / RAW / "Types.lean")
    require(set(types) == {name for names in TYPES.values() for name in names}, "finish generated type set differs")
    for path, names in TYPES.items():
        shared = declarations(root / path)
        require(all(types[name] == shared[name] for name in names), "finish shared type differs: " + path)
    externals = declarations(root / RAW / "FunsExternal_Template.lean")
    for name, path in CALLEES.items():
        require(verify.signature(externals[name]) == verify.signature(declarations(root / path)[name]),
                "finish original callee signature differs: " + name)
    source = root / RAW / "Funs.lean"
    functions = declarations(source)
    require([name for name in functions if name.startswith(IMPL + ".finish")] == list(NAMES) and
            all("sorry" not in functions[name] for name in NAMES) and
            (root / ACTIVE).read_text() == project(source.read_text()), "compiled finish projection differs")
    return {
        "raw_generated_file": str(RAW / "Funs.lean"), "raw_file_sha256": OUTPUT_HASHES["Funs.lean"],
        "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
        "source_declarations_retained_verbatim": len(NAMES),
        "shared_types_and_function_dictionary_declarations_checked": True,
        "generated_declarations": ["bulksketch." + name for name in NAMES],
        "native_source_edited": False, "translator_variant": VARIANT,
    }


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
