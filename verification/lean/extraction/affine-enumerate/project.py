#!/usr/bin/env python3
"""Check the exact original affine enumerator extraction and its scoped translator evidence."""
import hashlib
import importlib.util
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/affine-enumerate")
RAW = DIRECTORY / "Arithmetic"
ACTIVE = Path("bridge/Arithmetic/AffineEnumerateGenerated.lean")


def import_at(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


setup = import_at("root_setup", ROOT / "extraction/root-setup/project.py")
flow = import_at("affine_control_flow", ROOT / DIRECTORY / "control_flow.py")
require, sha, declarations = setup.require, setup.sha, setup.declarations

VARIANT = "checked-affine-outer-continue-v1"
CAPTURE = flow.CAPTURE
SELECTOR = flow.SELECTOR
PATCH = DIRECTORY / "checked-affine-outer-continue.patch"
PATCH_HASH = "6481beb982e57655e7ee2c888daf823c9b5286f66af85f9ec56dac90e545aa4f"
PATCHED_BINARY = "9231c0ec71ada49e1cb5f6663706ff046afd8ad35bc1af42edeae11d954a8645"
BASE_SOURCE = "ae752eeef3227b7566611fa7d3ace71fd64fbf24c088bc7ce16699a243772165"
VARIANT_SOURCE = "d0d2a6a122bc0446a493b4d70ff2ca19fc53122c4ab6ee0e3192343d082fb8eb"
SOURCE_HASHES = {
    "src/decode/affine.rs": "a7c45498717202aec291b4c4acdd6f819edf16bcdf478500a8c74a3492c4e11d",
    "src/backend/contract.rs": "4d05ce564edc408ba04f5a907b159ad91018ba8cfd93126e17913ed49f7e3d59",
    "src/types.rs": "5702a8552c1158cf69f2155d2484f246f87475dc6bef3ea734be52348acd940d",
}
HEADER = "d63415340566d2ceb7cbeda45239b676a59a81c8e85cb7eaef3898bfcd00a817"
MARKER = "/-- [bulksketch::decode::affine::enumerate]: loop body 1:"
NAME = "decode.affine.enumerate"
FUNS = tuple(NAME + suffix for suffix in (
    "_loop0_loop0.body", "_loop0_loop0", "_loop0_loop1.body", "_loop0_loop1",
    "_loop0.body", "_loop0", "",
))
OUTPUT_HASHES = {
    "Funs.lean": "7d2317640c55722bd5472bbaad51f84a0af5449faaa9f2508af83ce6c42dc481",
    "FunsExternal_Template.lean": "9c0b9bc7263142cde8a1ff14d9377ddc2ba386acbaf4158a46d429fd062eb803",
    "Types.lean": "ec25fe10cf04ff6687064fa9b18f8a40bc1ac761f2f643b99db946ccb38b62ac",
}
OUTPUTS = tuple(OUTPUT_HASHES)
SHARED_TYPES = {
    "Types.lean": ("types.RawProduct", "types.FieldId", "field.sealed.Sealed", "field.BinaryField"),
    "SliceKernelTypes.lean": ("backend.contract.Arithmetic", "backend.contract.BulkKernels"),
    "ReconstructionTypes.lean": ("types.DecodeFailure",),
}
COMPATIBLE = ("root-enumerate-affine", "affine-splitter")
GUARDS = ("wrong-name", "wrong-span", "wrong-cleanup", "wrong-break", "wrong-constructor")
CONTROLS = {"stock": 1, "checked": 0, "unchecked": 1, **dict.fromkeys(GUARDS, 1), **dict.fromkeys(COMPATIBLE, 0)}
REJECTION = "Continue to outer loops are not supported yet"
ARTIFACTS = {str(RAW / name) for name in OUTPUTS} | {str(PATCH)}
ARTIFACTS |= {str(DIRECTORY / name) for name in (
    "arithmetic.llbc", "charon.log", "fresh-build.log", "replay.log",
    "control_flow.py", "guard-controls.py", "return-place.log", "missing-return-assignment.log",
)}
ARTIFACTS |= {str(DIRECTORY / (name + ".log")) for name in CONTROLS}


def sha_bytes(value):
    return hashlib.sha256(value).hexdigest()


def output_hashes(root, base):
    return {name: sha(root / base / name) for name in OUTPUTS}


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    require(receipt["variant_id"] == VARIANT and receipt["source_commit"] == setup.SOURCE
            and receipt["aeneas_commit"] == setup.AENEAS and receipt["charon_commit"] == setup.CHARON
            and receipt["target"] == setup.TARGET and receipt["rust_toolchain"] == "nightly-2026-09-17"
            and receipt["native_source_edited"] is False and receipt["native_llbc_edited"] is False
            and receipt["source_sha256"] == SOURCE_HASHES and receipt["capture_sha256"] == CAPTURE
            and receipt["variant_patch"] == str(PATCH) and receipt["variant_patch_sha256"] == PATCH_HASH
            and receipt["patched_binary_sha256"] == PATCHED_BINARY
            and receipt["base_sources"] == {"src/PrePasses.ml": BASE_SOURCE}
            and receipt["modified_sources"] == {"src/PrePasses.ml": VARIANT_SOURCE}
            and set(receipt["files_sha256"]) == ARTIFACTS, "invalid affine enumerator receipt")
    for path, expected in receipt["files_sha256"].items():
        require(sha(root / path) == expected, "affine enumerator artifact differs: " + path)
    require(sha(root / PATCH) == PATCH_HASH, "affine enumerator translator patch differs")
    llbc_path = root / DIRECTORY / "arithmetic.llbc"
    require(sha(llbc_path) == CAPTURE, "original affine enumerator LLBC differs")
    llbc = flow.frozen_capture(llbc_path.read_bytes())
    crate = llbc["translated"]
    for path, digest in SOURCE_HASHES.items():
        require(sha(root.parents[1] / path) == digest, "pinned affine enumerator source differs: " + path)
        embedded = [file["contents"] for file in crate["files"] if file and file["name"] == {"Local": path}]
        require(len(embedded) == 1 and sha_bytes(embedded[0].encode()) == digest,
                "embedded affine enumerator source differs: " + path)
    opts, targets = crate["options"], crate["target_information"]
    require(llbc["has_errors"] is False and opts["start_from"] == [SELECTOR] and opts["opaque"] == []
            and len(targets) == 1 and targets[0]["key"] == setup.TARGET
            and targets[0]["value"]["target_pointer_size"] == 8,
            "affine enumerator extraction scope or target differs")
    decl, body = flow.enumerate_body(llbc)
    span = decl["item_meta"]["span"]["Untagged"]
    source = span["data"]
    require(span["generated_from_span"] is None and crate["files"][source["file_id"]]["name"] ==
            {"Local": "src/decode/affine.rs"} and source["beg"] == {"line": 302, "col": 0}
            and source["end"] == {"line": 347, "col": 1}, "original affine enumerator source span differs")
    flow.check_shape(body)

    parent = json.loads((root / "extraction/root-setup/receipt.json").read_text())
    manifest = next(word for word in parent["charon_command"] if word.startswith("--manifest-path="))
    evidence = Path(manifest.removeprefix("--manifest-path=")).parent.parent / (
        "bulksketch-proof-evidence-20261109-native-root-run/roots-enumerate-affine/original-affine-enumerate")
    original_capture = evidence / "arithmetic.llbc"
    require(opts["dest_file"] == str(original_capture)
            and receipt["charon_exit"] == 0
            and receipt["charon_binary_sha256"] == setup.BINARY_SHA256["charon"]
            and receipt["charon_command"] == [parent["charon_command"][0], "cargo", "--preset=aeneas",
                "--sysroot=default", "--dest-file=" + str(original_capture), "--start-from=" + SELECTOR, "--",
                manifest, "-p", "bulksketch", "--lib", "--locked", "--target", setup.TARGET],
            "affine enumerator recorded Charon command differs")
    outputs = output_hashes(root, RAW)
    require(outputs == OUTPUT_HASHES, "frozen affine enumerator Lean artifacts differ")
    replay, build = receipt["replay"], receipt["fresh_build"]
    clean_src = evidence / "rebuilt-affine-scoped/src"
    fresh_binary = str(clean_src / "_build/default/main.exe")
    require(build["exit_code"] == 0 and build["source_sha256"] == VARIANT_SOURCE
            and build["source_files_byte_identical"] == 108
            and build["command"] == ["opam", "exec", "--root=" + str(evidence.parents[2] /
                    "bulksketch-proofs/tooling/opam-root"), "--switch=aeneas-5.3.0", "--",
                "dune", "build", "--root", str(clean_src), "-j", "2"]
            and build["log_sha256"] == sha(root / DIRECTORY / "fresh-build.log")
            and replay["command"] == [fresh_binary, *setup.FLAGS, str(evidence / "fresh-scoped-replay"),
                str(original_capture)]
            and replay["exit_code"] == 0 and replay["binary_sha256"] == receipt["patched_binary_sha256"]
            and replay["input_sha256"] == CAPTURE and replay["outputs"] == outputs
            and replay["log_sha256"] == sha(root / DIRECTORY / "replay.log"),
            "affine enumerator checked clean-build replay differs")

    controls = receipt["controls"]
    require(set(controls) == set(CONTROLS) | {"return-place", "missing-return-assignment"},
            "incomplete affine enumerator controls")
    control_dir = evidence / "scoped-guard-controls"
    historical_root = Path(manifest.removeprefix("--manifest-path=")).parent / "verification/lean"
    for name, exit_code in CONTROLS.items():
        row = controls[name]
        binary = setup.BINARY_SHA256["aeneas"] if name == "stock" else receipt["patched_binary_sha256"]
        binary_path = parent["aeneas_command"][0] if name == "stock" else fresh_binary
        if name in COMPATIBLE:
            other = Path("extraction") / name
            input_hash = sha(root / other / "arithmetic.llbc")
            expected = output_hashes(root, other / "Arithmetic")
            input_file = historical_root / other / "arithmetic.llbc"
        elif name in GUARDS:
            input_hash = sha_bytes(flow.altered_capture(llbc, name))
            input_file = control_dir / name / "arithmetic.llbc"
            expected = {}
        else:
            input_hash = CAPTURE
            input_file = historical_root / DIRECTORY / "arithmetic.llbc"
            expected = {} if exit_code else outputs
        log = root / DIRECTORY / (name + ".log")
        command = row["command"]
        require(row["exit_code"] == exit_code and row["binary_sha256"] == binary
                and row["input_sha256"] == input_hash and row["outputs"] == expected
                and command[0] == binary_path
                and command[1:-2] == [flag for flag in setup.FLAGS if flag != "-checks" or name != "unchecked"]
                and command[-2:] == [str(control_dir / name / "generated"), str(input_file)]
                and row["log_sha256"] == sha(log) and (exit_code == 0 or REJECTION in log.read_text()),
                "affine enumerator control differs: " + name)
    normal = root / DIRECTORY / "return-place.log"
    require(controls["return-place"] == {"input_sha256": CAPTURE, "log_sha256": sha(normal)}
            and normal.read_text() == flow.check_return_place(body) + "\n", "affine return-place check differs")
    altered = flow.altered_capture(llbc, "missing-return-assignment")
    _, negative_body = flow.enumerate_body(json.loads(altered))
    try:
        flow.check_return_place(negative_body)
    except ValueError as error:
        reason = str(error)
    else:
        raise ValueError("missing original affine return assignment was accepted")
    negative = root / DIRECTORY / "missing-return-assignment.log"
    require(controls["missing-return-assignment"] == {"input_sha256": sha_bytes(altered), "log_sha256": sha(negative)}
            and reason == "return 1188 reachable without a fresh result assignment"
            and negative.read_text() == reason + "\n", "affine return-place negative differs")

    types = declarations(root / RAW / "Types.lean")
    require(set(types) == {name for names in SHARED_TYPES.values() for name in names},
            "affine enumerator shared type set differs")
    for file, names in SHARED_TYPES.items():
        existing = declarations(root / "bridge/Arithmetic" / file)
        require(all(types[name] == existing.get(name) for name in names),
                "affine enumerator shared type differs: " + file)
    require(set(re.findall(r"^axiom (\S+)", (root / RAW / "FunsExternal_Template.lean").read_text(), re.M))
            == {"core.num.Usize.checked_shl", "core.num.Usize.trailing_zeros", "core.slice.raw.from_ref"},
            "affine enumerator unexpected opaque callee")
    functions = declarations(root / RAW / "Funs.lean")
    require([name for name in functions if name.startswith(NAME)] == list(FUNS),
            "original affine enumerator generated body set differs")
    header, marker, body = (root / ACTIVE).read_text().partition(MARKER)
    require(sha_bytes(header.encode()) == HEADER
            and marker + body == "\n\n".join(functions[name] for name in FUNS) + "\nend bulksketch\n",
            "compiled affine enumerator projection differs")
    return {
        "raw_generated_file": str(RAW / "Funs.lean"), "raw_file_sha256": sha(root / RAW / "Funs.lean"),
        "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
        "source_declarations_retained_verbatim": len(FUNS),
        "shared_types_and_function_dictionary_declarations_checked": True,
        "generated_declarations": ["bulksketch." + name for name in FUNS],
        "native_source_edited": False,
        "translator_variant": VARIANT,
    }


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
