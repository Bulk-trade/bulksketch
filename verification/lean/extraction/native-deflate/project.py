#!/usr/bin/env python3
"""Verify the original deflate capture, scoped translator controls and exact projection."""
import hashlib
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/native-deflate")
RAW = DIRECTORY / "Arithmetic"
ACTIVE = Path("bridge/Arithmetic/NativeDeflateGenerated.lean")
COMPAT = Path("extraction/execution-verify")


def import_at(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


setup = import_at("deflate_root_setup", ROOT / "extraction/root-setup/project.py")
verify = import_at("deflate_execution_verify", ROOT / COMPAT / "project.py")
mutation = import_at("wrong_roots_loan", ROOT / DIRECTORY / "wrong_roots_loan.py")
require, sha, declarations = verify.require, verify.sha, verify.declarations

VARIANT = "checked-native-deflate-loan-retry-v1"
PATCH = DIRECTORY / "checked-native-deflate-loan-retry.patch"
PATCH_HASH = "0e6309acb7a82f7012d4bec0fe5c5c5a7ed58f9d177077f0927eaef5e3ce37b3"
CAPTURE = mutation.CAPTURE
RECAPTURE = "5eb349b0f8ea2373900bba90de9d81aa371a527ebca791c937cce7b6b33ef29e"
WRONG_OWNER = "b1262c48129e19991c20737dd9e079be0632598eb575554aec52412de25199a0"
PATCHED_BINARY = "f0b3dc38ea654328e7480355682b1fb6a527e226fb66d714cdb760b377e246da"
BASE_SOURCES = {"src/interp/InterpMatchCtxs.ml": "a97bd2650a71ec0795f570dac17a8a1f1f52ae2b6feb4619984e6f1d61fde264"}
MODIFIED_SOURCES = {"src/interp/InterpMatchCtxs.ml": "a24cdbb56f8220eb881ecf33d76654eb9b7f92c85757834e37e4b2194d8bb931"}
OUTPUT_HASHES = {
    "Funs.lean": "e41d85f34becf7435c75136c0bf6b4eff9a8b1f14c806ef34cfea6a2e00dd1b9",
    "Types.lean": "5b2de071521a639ce8e4cc56a69c8f01f0116b8a37d4bc1036f660a0daed52b8",
    "FunsExternal_Template.lean": "19dcf55935884b26471e1a3ea81af2b219d11cd4326a08dab75e542432159333",
}
SOURCE_HASHES = {
    "src/lib.rs": "5174f3741a1c1b0bbdfddfac894adb8d96de06896dce8960bad76fe2056fe124",
    "src/decode/mod.rs": "4d1f559feaa82a6f89e4ddd533fb7fa526d5637386364385020888c25e6026b4",
    "src/decode/stages.rs": "93825fcb5054e98e9af060a81da72d4770c29354d79822ccfc949cc55f6e9b23",
    "src/types.rs": "5702a8552c1158cf69f2155d2484f246f87475dc6bef3ea734be52348acd940d",
    "src/decode/row.rs": "bf5ae89114d3bab811f1e0ca3b370cd916803bddd178471b3167e81b432df7bc",
    "src/decode/roots.rs": "4697d5874fd1eb03c0210371fdac83a8dc7171de2724da046613f59c879f4fb6",
    "src/decode/degree_probe.rs": "60d72b0aa11f311c4359bfe94f0d6fede00723602b3251492cbdb10ee51752ed",
    "src/field/mod.rs": "035dc6193ebb50b324527525c0ee47cbe06ca325db16aa5f8ee55b0e79baa723",
    "src/backend/mod.rs": "b4883e5070592cd5db4c9450fbc14e7dc9c07ec457029a54917295a24a94fb72",
    "src/backend/contract.rs": "4d05ce564edc408ba04f5a907b159ad91018ba8cfd93126e17913ed49f7e3d59",
    "src/decode/scratch.rs": "97016cadabf021829b567ff1472a9f11136f54059d78e457d58896cc318e50f6",
    "src/decode/work.rs": "c0a9bbdc839f889502e7b6b3f2960649c2bc71000b3e787f613b3fc8c23ac3af",
}
STAGES = "bulksketch::decode::stages"
SELECTOR = STAGES + "::_::deflate"
OPAQUE = [STAGES + "::_::_", STAGES + "::check_workspace",
          "bulksketch::decode::roots::_::start", "bulksketch::poly::dense::_::eval_many_into"]
SPANS = {
    "deflate": ("src/decode/stages.rs", 304, 4, 333, 5),
    "charge": ("src/decode/stages.rs", 163, 4, 165, 5),
    "start": ("src/decode/roots.rs", 86, 4, 98, 5),
}
NAME = "decode.stages.Execution.deflate"
FUNCTIONS = tuple(NAME + suffix for suffix in ("_loop0_loop0.body", "_loop0_loop0", "_loop0.body", "_loop0", ""))
CALLEES = {
    "decode.stages.Execution.charge": "bridge/Arithmetic/WorkScheduleGenerated.lean",
    "decode.roots.Roots.start": "bridge/Arithmetic/RootSetupGenerated.lean",
}
FLAG = {"BULKSKETCH_DEFLATE": "1"}
FLAGS = ["-backend", "lean", "-sequential", "-no-progress-bar", "-print-error-emitters", "-split-files"]
CONTROLS = {"stock": 1, "flag-off": 1, "unchecked": 1, "checked": 0,
            "wrong-roots-loan": 1, "execution-verify": 0}
ARTIFACTS = {str(RAW / name) for name in OUTPUT_HASHES} | {str(PATCH)}
ARTIFACTS |= {str(DIRECTORY / name) for name in (
    "arithmetic.llbc", "charon.log", "fresh-build.log", "wrong_roots_loan.py", "guard-controls.py",
)}
ARTIFACTS |= {str(DIRECTORY / (name + ".log")) for name in CONTROLS}
HEADER = """-- Checked original deflate projection with the scoped return-join retry.
import Arithmetic.ExecutionVerifyGenerated
import Arithmetic.RootSetupGenerated

open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxRecDepth 4096
set_option linter.unusedVariables false

namespace bulksketch

"""
MARKER = "/-- [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::deflate]"


def sha_bytes(data):
    return hashlib.sha256(data).hexdigest()


def output_hashes(root, directory):
    return {name: sha(root / directory / name) for name in OUTPUT_HASHES}


def check_llbc(root, data):
    llbc = mutation.load(data)
    crate = llbc["translated"]
    options, targets = crate["options"], crate["target_information"]
    require(llbc["has_errors"] is False and options["start_from"] == [STAGES] and
            options["include"] == [SELECTOR] and options["opaque"] == OPAQUE and
            len(targets) == 1 and targets[0]["key"] == setup.TARGET and
            targets[0]["value"]["target_pointer_size"] == 8, "deflate capture options or target differ")
    for path, digest in SOURCE_HASHES.items():
        require(sha(root.parents[1] / path) == digest, "pinned deflate source differs: " + path)
        embedded = [entry["contents"] for entry in crate["files"] if entry and entry["name"] == {"Local": path}]
        require(len(embedded) == 1 and sha_bytes(embedded[0].encode()) == digest,
                "embedded deflate source differs: " + path)
    seen = set()
    for function in crate["fun_decls"]:
        if not function:
            continue
        meta = function["item_meta"]
        name = meta["name"][-1].get("Ident", [None])[0]
        span = meta["span"]["Untagged"]
        loc = span["data"]
        path = crate["files"][loc["file_id"]]["name"].get("Local")
        if name not in SPANS or path != SPANS[name][0]:
            continue
        _, start, start_col, end, end_col = SPANS[name]
        require(name not in seen and span["generated_from_span"] is None and
                loc["beg"] == {"line": start, "col": start_col} and loc["end"] == {"line": end, "col": end_col} and
                (function == mutation.select(llbc) if name == "deflate" else function["body"] == "Opaque"),
                "deflate or verified callee span changed: " + name)
        seen.add(name)
    require(seen == SPANS.keys(), "original deflate or its checked callees are missing")
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
            "invalid deflate translator receipt")
    for path, expected in receipt["files_sha256"].items():
        require(sha(root / path) == expected, "deflate artifact differs: " + path)
    require(sha(root / PATCH) == PATCH_HASH, "deflate translator patch differs")

    parent = json.loads((root / "extraction/root-setup/receipt.json").read_text())
    manifest = next(word for word in parent["charon_command"] if word.startswith("--manifest-path="))
    native_repo = Path(manifest.removeprefix("--manifest-path=")).parent
    evidence = native_repo.parent / "bulksketch-proof-evidence-20261109-decoder-deflation"
    require(original == evidence / "deflate/arithmetic.llbc", "deflate historical capture path differs")
    rebuilt = evidence / "fresh-deflate-tool/src"
    patched = rebuilt / "_build/default/main.exe"
    recapture = original.with_name("recaptured.llbc")
    command = [parent["charon_command"][0], "cargo", "--preset=aeneas", "--sysroot=default",
               "--dest-file=" + str(recapture), "--start-from=" + STAGES, "--opaque=" + OPAQUE[0],
               "--include=" + SELECTOR, *("--opaque=" + name for name in OPAQUE[1:]), "--",
               manifest, "-p", "bulksketch", "--lib", "--locked", "--target", setup.TARGET]
    require(receipt["charon_recapture"] == {
        "command": command, "exit_code": 0, "binary_sha256": setup.BINARY_SHA256["charon"],
        "original_sha256": CAPTURE, "recapture_sha256": RECAPTURE,
        "normalized_fields": ["translated.options.dest_file"],
        "log_sha256": sha(root / DIRECTORY / "charon.log"),
    } and sha_bytes(data.replace(str(original).encode(), str(recapture).encode(), 1)) == RECAPTURE,
        "deflate stock Charon recapture differs beyond the destination")
    require(receipt["fresh_build"] == {
        "command": ["dune", "build", "--root", str(rebuilt), "-j", "2", "./main.exe"],
        "exit_code": 0, "source_files_byte_identical": 108,
        "modified_source_sha256": MODIFIED_SOURCES, "log_sha256": sha(root / DIRECTORY / "fresh-build.log"),
    }, "deflate checked fresh build differs")

    controls = receipt["controls"]
    require(set(controls) == set(CONTROLS), "incomplete deflate translator controls")
    require(receipt["replay"] == controls["checked"], "deflate replay lost its checked control linkage")
    control_dir = evidence / "fresh-deflate-controls"
    compatibility = native_repo / "verification/lean" / COMPAT
    require(sha_bytes(mutation.wrong_owner(data)) == WRONG_OWNER, "deflate wrong-owner mutation differs")
    for name, status in CONTROLS.items():
        log = root / DIRECTORY / (name + ".log")
        if status:
            diagnostic = log.read_text()
            require("Internal error" in diagnostic and "Could not translate the body" in diagnostic and
                    "Source: 'src/decode/stages.rs', lines 321:8-333:5" in diagnostic and
                    "Compiler source: interp/InterpMatchCtxs.ml, line 649" in diagnostic,
                    "deflate control rejection moved: " + name)
        tool = parent["aeneas_command"][0] if name == "stock" else str(patched)
        if name == "execution-verify":
            source = compatibility / "arithmetic.llbc"
            input_digest = sha(root / COMPAT / "arithmetic.llbc")
            outputs = output_hashes(root, COMPAT / "Arithmetic")
        elif name == "wrong-roots-loan":
            source = control_dir / "wrong-roots-loan.llbc"
            input_digest, outputs = WRONG_OWNER, {}
        else:
            source = original
            input_digest, outputs = CAPTURE, {} if status else OUTPUT_HASHES
        require(controls[name] == {
            "command": [tool, *FLAGS, *(["-checks"] if name != "unchecked" else []),
                        "-dest", str(control_dir / name), str(source)],
            "environment": {} if name in ("stock", "flag-off") else FLAG, "exit_code": status,
            "binary_sha256": setup.BINARY_SHA256["aeneas"] if name == "stock" else PATCHED_BINARY,
            "input_sha256": input_digest, "log_sha256": sha(log), "outputs": outputs,
        }, "deflate control differs: " + name)


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    data = (root / DIRECTORY / "arithmetic.llbc").read_bytes()
    original = check_llbc(root, data)
    check_receipt(root, receipt, original, data)
    require(output_hashes(root, RAW) == OUTPUT_HASHES, "frozen deflate generated Lean differs")
    types = declarations(root / RAW / "Types.lean")
    for path, names in verify.TYPE_DEPENDENCIES.items():
        shared = declarations(root / path)
        require(all(types[name] == shared[name] for name in names), "deflate shared type differs: " + path)
    external = declarations(root / RAW / "FunsExternal_Template.lean")
    for name, path in CALLEES.items():
        require(verify.signature(external[name]) == verify.signature(declarations(root / path)[name]),
                "deflate checked callee signature differs: " + name)
    source = root / RAW / "Funs.lean"
    names = declarations(source)
    require([name for name in names if name.startswith(NAME)] == list(FUNCTIONS),
            "deflate generated declaration set differs")
    _, marker, suffix = source.read_text().partition(MARKER)
    require(marker and "sorry" not in suffix and (root / ACTIVE).read_text() == HEADER + marker + suffix,
            "compiled deflate projection differs")
    return {
        "raw_generated_file": str(RAW / "Funs.lean"), "raw_file_sha256": OUTPUT_HASHES["Funs.lean"],
        "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
        "source_declarations_retained_verbatim": len(FUNCTIONS),
        "shared_types_and_function_dictionary_declarations_checked": True,
        "generated_declarations": ["bulksketch." + name for name in FUNCTIONS],
        "native_source_edited": False, "translator_variant": VARIANT,
    }


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
