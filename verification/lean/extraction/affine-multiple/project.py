#!/usr/bin/env python3
"""Check exact original affine multiple extraction and scoped translator provenance."""
import hashlib
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/affine-multiple")
RAW = DIRECTORY / "Arithmetic"
ACTIVE = Path("bridge/Arithmetic/AffineMultipleGenerated.lean")


def import_at(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


setup = import_at("root_setup", ROOT / "extraction/root-setup/project.py")
lifetimes = import_at("affine_multiple_zip_lifetimes", ROOT / DIRECTORY / "zip_lifetimes.py")
require, sha, declarations = setup.require, setup.sha, setup.declarations

VARIANT = "checked-affine-multiple-zip-ends-v1"
CAPTURE = lifetimes.CAPTURE
SELECTOR = lifetimes.SELECTOR
PATCH = DIRECTORY / "checked-affine-multiple-zip-ends.patch"
PATCH_HASH = "ee10ff36dfc11a6fe78b6789b775e4afbb4b2a3171458d37a599a9eae111e9c9"
PATCHED_BINARY = "53fd011bcc11b7107f4783b8cf1e98ce9ff8080b2b13efa68319abb321bc723b"
RECAPTURE = "45089f9f04ea6f8612bf93f6b0be4f65a522ae810194b465167d67cf369b83f8"
HEADER = "3c2da779200e880360936e8cf8d35c7f549bf12b7131de34c9cb20ded6dbb6a6"
MARKER = "/-- [bulksketch::decode::affine::multiple]: loop body 1:"
NAME = "decode.affine.multiple"
FUNS = tuple(NAME + suffix for suffix in (
    "_loop0_loop0.body", "_loop0_loop0", "_loop0_loop1.body", "_loop0_loop1",
    "_loop0_loop2.body", "_loop0_loop2", "_loop0.body", "_loop0", "",
))
OUTPUT_HASHES = {
    "Funs.lean": "c016c3f963dbe2708027b8e039a0c7590191864a6bcd17468e89e76fca38b7cc",
    "FunsExternal_Template.lean": "6b79b38a224de70ad04c51859800b4fc780fbe31c9da077306463d61ffdbefa3",
    "Types.lean": "8a93715ef2336aafd7a6e2441962da32c9298cbfcc57058f0cbea7e3d1718471",
}
SOURCE_HASHES = {
    "src/decode/affine.rs": "a7c45498717202aec291b4c4acdd6f819edf16bcdf478500a8c74a3492c4e11d",
    "src/poly/dense.rs": "13b360fba6387dda36a9655f3f67d01be6752e4ca6b7f8e1824e7333bf3da644",
    "src/backend/contract.rs": "4d05ce564edc408ba04f5a907b159ad91018ba8cfd93126e17913ed49f7e3d59",
    "src/types.rs": "5702a8552c1158cf69f2155d2484f246f87475dc6bef3ea734be52348acd940d",
}
BASE_SOURCES = {
    "src/interp/InterpStatements.ml": "52ff1eb23a3b02b969fbbd38849f58e27d8652253a3c7bf996e7a19e747f32a0",
    "src/interp/InterpBorrows.ml": "41fe2d959370354e5187007eb358088883a196ebc44f6635511f215dba332a7a",
    "src/interp/InterpBorrows.mli": "bec35be5ccd34bc596d23deaa4f1f4b93358759a385e9f55bef794c26d8ebcba",
    "src/interp/InterpBorrowsCore.ml": "0294abaaf5a305ef73f19c807626e37e55023f52c9fb0e7abda86bfdcbf1db89",
    "src/interp/InterpAbs.ml": "713c57546138df421b391293a76e175391f2ecbcf4b3d97db7e9e6c93c89de0b",
}
VARIANT_SOURCES = {
    "src/interp/InterpStatements.ml": "d8501e596eb0f22e3fbe2738f5f8a450b88824467371a96297de1fdc3ac7089b",
    "src/interp/InterpBorrows.ml": "15e67c132d27eae2d463ad84cd870c2714e77f231958a887d35696bb47cb5cb2",
    "src/interp/InterpBorrows.mli": "e796730bdedccb563e4271be55b341b8e2118dd5ecc5a60f7406a0460d4a6a9b",
    "src/interp/InterpBorrowsCore.ml": "002da3564d478de1af820e6b86a139e5c8fbe94ff2b2f982ffd142025b78ebf2",
    "src/interp/InterpAbs.ml": "e848a941e6bbff0c33cf2d84da9688e3dd3c91690b9f6deb4b5ca8eee07583d7",
}
SHARED_TYPES = {
    "Types.lean": ("types.RawProduct", "types.FieldId", "field.sealed.Sealed", "field.BinaryField"),
    "SliceKernelTypes.lean": ("backend.contract.Arithmetic", "backend.contract.BulkKernels"),
    "RebuiltLfsrTypes.lean": ("core.ops.range.RangeToInclusive",),
}
CONTROLS = {"stock": 1, "flag-off": 1, "unchecked": 1, "checked": 0, "wrong-lifetime": 1, "affine-splitter": 0}
FLAG = {"BULKSKETCH_AFFINE_MULTIPLE": "1"}
CONTROL_FLAGS = ["-backend", "lean", "-sequential", "-no-progress-bar", "-print-error-emitters", "-split-files"]
ARTIFACTS = {str(RAW / name) for name in OUTPUT_HASHES} | {str(PATCH)}
ARTIFACTS |= {str(DIRECTORY / name) for name in (
    "arithmetic.llbc", "charon.log", "fresh-build.log", "replay.log",
    "zip_lifetimes.py", "guard-controls.py", "zip-lifetimes.log",
)}
ARTIFACTS |= {str(DIRECTORY / (name + ".log")) for name in CONTROLS}


def sha_bytes(value):
    return hashlib.sha256(value).hexdigest()


def output_hashes(root, base):
    return {name: sha(root / base / name) for name in OUTPUT_HASHES}


def local_span(crate, decl):
    span = decl["item_meta"]["span"]["Untagged"]
    info = span["data"]
    return crate["files"][info["file_id"]]["name"], info["beg"], info["end"], span["generated_from_span"]


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    require(receipt["variant_id"] == VARIANT and receipt["source_commit"] == setup.SOURCE
            and receipt["aeneas_commit"] == setup.AENEAS and receipt["charon_commit"] == setup.CHARON
            and receipt["target"] == setup.TARGET and receipt["rust_toolchain"] == "nightly-2026-09-17"
            and receipt["native_source_edited"] is False and receipt["native_llbc_edited"] is False
            and receipt["source_sha256"] == SOURCE_HASHES and receipt["capture_sha256"] == CAPTURE
            and receipt["variant_patch"] == str(PATCH) and receipt["variant_patch_sha256"] == PATCH_HASH
            and receipt["patched_binary_sha256"] == PATCHED_BINARY
            and receipt["base_sources"] == BASE_SOURCES and receipt["modified_sources"] == VARIANT_SOURCES
            and set(receipt["files_sha256"]) == ARTIFACTS, "invalid affine multiple receipt")
    for path, expected in receipt["files_sha256"].items():
        require(sha(root / path) == expected, "affine multiple artifact differs: " + path)
    require(sha(root / PATCH) == PATCH_HASH, "affine multiple translator patch differs")
    llbc_path = root / DIRECTORY / "arithmetic.llbc"
    contents = llbc_path.read_bytes()
    llbc = lifetimes.load(contents)
    crate = llbc["translated"]
    for path, digest in SOURCE_HASHES.items():
        require(sha(root.parents[1] / path) == digest, "pinned affine multiple source differs: " + path)
        embedded = [file["contents"] for file in crate["files"] if file and file["name"] == {"Local": path}]
        require(len(embedded) == 1 and sha_bytes(embedded[0].encode()) == digest,
                "embedded affine multiple source differs: " + path)
    opts, targets = crate["options"], crate["target_information"]
    require(llbc["has_errors"] is False and opts["start_from"] == [SELECTOR] and opts["opaque"] == lifetimes.OPAQUE
            and len(targets) == 1 and targets[0]["key"] == setup.TARGET
            and targets[0]["value"]["target_pointer_size"] == 8,
            "affine multiple extraction scope or target differs")
    decl = lifetimes.select(llbc)
    require(isinstance(decl["body"], dict) and "Structured" in decl["body"]
            and local_span(crate, decl) == ({"Local": "src/decode/affine.rs"}, {"line": 100, "col": 0},
                                            {"line": 170, "col": 1}, None),
            "original affine multiple source span or body differs")
    opaque = [fn for fn in crate["fun_decls"] if fn and fn["body"] == "Opaque"
              and local_span(crate, fn)[0].get("Local", "").startswith("src/")]
    require(len(opaque) == 1 and opaque[0]["item_meta"]["name"][-1].get("Ident") == ["square_mod_into", 0]
            and local_span(crate, opaque[0]) ==
                ({"Local": "src/poly/dense.rs"}, {"line": 188, "col": 4}, {"line": 224, "col": 5}, None),
            "affine multiple opaque Dense callback differs")
    require((root / DIRECTORY / "zip-lifetimes.log").read_text() == lifetimes.lifetime_shapes(llbc),
            "affine multiple lifetime check differs")

    parent = json.loads((root / "extraction/root-setup/receipt.json").read_text())
    manifest = next(word for word in parent["charon_command"] if word.startswith("--manifest-path="))
    repo_path = Path(manifest.removeprefix("--manifest-path=")).parent
    evidence = repo_path.parent / "bulksketch-proof-evidence-20261109-affine-native/affine-multiple"
    original_capture = evidence / "arithmetic.llbc"
    recapture = receipt["charon_recapture"]
    require(opts["dest_file"] == str(original_capture)
            and recapture["command"] == [parent["charon_command"][0], "cargo", "--preset=aeneas",
                "--sysroot=default", "--dest-file=" + str(evidence / "recaptured.llbc"), "--start-from=" + SELECTOR,
                *("--opaque=" + name for name in lifetimes.OPAQUE), "--",
                manifest, "-p", "bulksketch", "--lib", "--locked", "--target", setup.TARGET]
            and recapture["exit_code"] == 0 and recapture["binary_sha256"] == setup.BINARY_SHA256["charon"]
            and recapture["original_sha256"] == CAPTURE and recapture["recapture_sha256"] == RECAPTURE
            and recapture["normalized_fields"] == ["translated.options.dest_file"]
            and recapture["log_sha256"] == sha(root / DIRECTORY / "charon.log"),
            "affine multiple stock Charon recapture differs")
    outputs = output_hashes(root, RAW)
    require(outputs == OUTPUT_HASHES, "frozen affine multiple generated Lean differs")
    replay, build = receipt["replay"], receipt["fresh_build"]
    clean_src = evidence / "fresh-checked-zip-tool/src"
    fresh_binary = str(clean_src / "_build/default/main.exe")
    require(build["exit_code"] == 0 and build["source_files_byte_identical"] == 104
            and build["modified_source_sha256"] == VARIANT_SOURCES
            and build["command"] == ["opam", "exec", "--root=" + str(repo_path.parent /
                    "bulksketch-proofs/tooling/opam-root"), "--switch=aeneas-5.3.0", "--",
                "dune", "build", "--root", str(clean_src), "-j", "2"]
            and build["log_sha256"] == sha(root / DIRECTORY / "fresh-build.log")
            and replay["command"] == [fresh_binary, *setup.FLAGS, str(evidence / "fresh-checked-zip-replay"),
                str(original_capture)]
            and replay["exit_code"] == 0 and replay["binary_sha256"] == receipt["patched_binary_sha256"]
            and replay["environment"] == FLAG and replay["input_sha256"] == CAPTURE and replay["outputs"] == outputs
            and replay["log_sha256"] == sha(root / DIRECTORY / "replay.log"),
            "affine multiple checked clean-build replay differs")

    controls = receipt["controls"]
    require(set(controls) == set(CONTROLS), "incomplete affine multiple controls")
    control_dir = evidence / "fresh-guard-controls"
    historical_root = repo_path / "verification/lean"
    for name, exit_code in CONTROLS.items():
        row = controls[name]
        binary = setup.BINARY_SHA256["aeneas"] if name == "stock" else receipt["patched_binary_sha256"]
        binary_path = parent["aeneas_command"][0] if name == "stock" else fresh_binary
        if name == "affine-splitter":
            other = Path("extraction/affine-splitter")
            input_hash = sha(root / other / "arithmetic.llbc")
            expected = output_hashes(root, other / "Arithmetic")
            input_file = historical_root / other / "arithmetic.llbc"
        elif name == "wrong-lifetime":
            input_hash = sha_bytes(lifetimes.wrong_lifetime(contents))
            expected = {}
            input_file = control_dir / name / "arithmetic.llbc"
        else:
            input_hash = CAPTURE
            expected = {} if exit_code else outputs
            input_file = historical_root / DIRECTORY / "arithmetic.llbc"
        log = root / DIRECTORY / (name + ".log")
        if exit_code:
            diagnostic = log.read_text()
            original_line = 2084 if name == "stock" else 2120
            require("Internal error" in diagnostic and "Source: 'src/decode/affine.rs', lines 119:4-170:1" in diagnostic
                    and f"Compiler source: interp/InterpBorrows.ml, line {original_line}" in diagnostic,
                    "affine multiple rejection moved: " + name)
        require(row["exit_code"] == exit_code and row["binary_sha256"] == binary
                and row["environment"] == ({} if name in {"stock", "flag-off"} else FLAG)
                and row["input_sha256"] == input_hash and row["outputs"] == expected
                and row["command"] == [binary_path, *CONTROL_FLAGS, *(["-checks"] if name != "unchecked" else []),
                    "-dest", str(control_dir / name / "generated"), str(input_file)]
                and row["log_sha256"] == sha(log),
                "affine multiple control differs: " + name)

    types = declarations(root / RAW / "Types.lean")
    require(set(types) == {name for names in SHARED_TYPES.values() for name in names},
            "affine multiple shared type set differs")
    for file, names in SHARED_TYPES.items():
        existing = declarations(root / "bridge/Arithmetic" / file)
        require(all(types[name] == existing.get(name) for name in names),
                "affine multiple shared type differs: " + file)
    functions = declarations(root / RAW / "Funs.lean")
    require([name for name in functions if name.startswith(NAME)] == list(FUNS),
            "original affine multiple generated body set differs")
    expected = []
    for name in FUNS:
        if name == NAME + "_loop0":
            expected.append(f'local notation "{NAME}_loop0.body" => ({NAME}_loop0.body squareModel)')
        if name == NAME:
            expected.append(f'local notation "{NAME}_loop0" => ({NAME}_loop0 squareModel)')
        expected.append(functions[name])
    header, marker, body = (root / ACTIVE).read_text().partition(MARKER)
    require(sha_bytes(header.encode()) == HEADER
            and marker + body == "\n\n".join(expected) + "\nend bulksketch\n",
            "compiled affine multiple projection differs")
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
