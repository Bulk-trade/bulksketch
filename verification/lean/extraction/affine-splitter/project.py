#!/usr/bin/env python3
"""Verify the original checked affine splitter projection."""
import hashlib
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SETUP = importlib.util.spec_from_file_location("root_setup", ROOT / "extraction/root-setup/project.py")
setup = importlib.util.module_from_spec(SETUP)
SETUP.loader.exec_module(setup)
require, sha, declarations = setup.require, setup.sha, setup.declarations

DIRECTORY = Path("extraction/affine-splitter")
RAW = DIRECTORY / "Arithmetic"
ACTIVE = Path("bridge/Arithmetic/AffineSplitterGenerated.lean")
NAME = "decode.affine.splitter"
SELECTOR = "bulksketch::decode::affine::splitter"
OPAQUE = ["bulksketch::poly::dense::_::square_mod_into", "bulksketch::decode::affine::linear_eval"]
TYPES = (NAME + ".closure_1", NAME + ".closure")
CALLBACK = NAME + ".closure.Insts.CoreOpsFunction"
INDEX = NAME + ".closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeUsize"
PREDICATE_ONCE = CALLBACK + "FnOnceTupleShared0U64Bool"
PREDICATE_MUT = CALLBACK + "FnMutTupleShared0U64Bool"
FUNS = (INDEX + ".call_once", INDEX, PREDICATE_MUT + ".call_mut", PREDICATE_ONCE + ".call_once",
        PREDICATE_ONCE, PREDICATE_MUT, NAME + "_loop.body", NAME + "_loop", NAME)
HEADER = """-- Exact checked source projection. See extraction/affine-splitter for provenance.
import Arithmetic.AffineLinearEvalGenerated
import Arithmetic.DenseNormalizationGenerated
import Arithmetic.RootTraceGenerated

open Aeneas Aeneas.Std Result ControlFlow Error

namespace bulksketch

set_option linter.dupNamespace false
set_option linter.unusedVariables false

variable (squareModel : Aeneas.Std.RootTraceRuntime.ModularSquare)

local notation "poly.Dense.Insts.BulksketchPolyPolynomial.square_mod_into" => squareModel

"""


def projection(root=ROOT):
    types = declarations(root / RAW / "Types.lean")
    funs = declarations(root / RAW / "Funs.lean")
    parts = [types[name] for name in TYPES]
    for name in FUNS:
        if name in (NAME + "_loop", NAME):
            callee = NAME + ("_loop.body" if name.endswith("_loop") else "_loop")
            parts.append(f'local notation "{callee}" => ({callee} squareModel)')
        parts.append(funs[name])
    return HEADER + "\n\n".join(parts) + "\nend bulksketch\n"


ARTIFACTS = {str(DIRECTORY / name) for name in (
    "arithmetic.llbc", "charon.log", "aeneas.log", "replay.log", "Arithmetic/Funs.lean",
    "Arithmetic/FunsExternal_Template.lean", "Arithmetic/Types.lean",
)}
SOURCES = ("src/decode/affine.rs", "src/poly/dense.rs")
SHARED = {
    "Types.lean": {"types.RawProduct", "types.FieldId", "field.sealed.Sealed", "field.BinaryField"},
    "SliceKernelTypes.lean": {"backend.contract.Arithmetic", "backend.contract.BulkKernels"},
}
EXPECTED = {
    ("splitter", SOURCES[0], 270, 297, "Structured"),
    ("linear_eval", SOURCES[0], 234, 243, "Opaque"),
    ("call_mut", SOURCES[0], 295, 295, "Structured"),
    ("call_once", SOURCES[0], 295, 295, "Structured"),
    ("call_once", SOURCES[0], 296, 296, "Structured"),
    ("square_mod_into", SOURCES[1], 188, 224, "Opaque"),
}


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    require(receipt["source_commit"] == setup.SOURCE and receipt["selector"] == SELECTOR
            and receipt["target"] == setup.TARGET and receipt["rust_toolchain"] == "nightly-2026-09-17"
            and receipt["aeneas_commit"] == setup.AENEAS and receipt["charon_commit"] == setup.CHARON
            and receipt["binary_sha256"] == setup.BINARY_SHA256 and receipt["native_source_edited"] is False
            and receipt["opaque_application_bodies"] == OPAQUE and receipt["checked_exit"] == 0
            and set(receipt["files_sha256"]) == ARTIFACTS, "invalid affine splitter receipt")
    for path, expected in receipt["files_sha256"].items():
        require(sha(root / path) == expected, "affine splitter artifact differs: " + path)
    parent = json.loads((root / "extraction/root-setup/receipt.json").read_text())
    manifest = next(word for word in parent["charon_command"] if word.startswith("--manifest-path="))
    destination = Path(manifest.removeprefix("--manifest-path=")).parent.parent / (
        "bulksketch-proof-evidence-20261109-affine-splitter/narrow-splitter/arithmetic.llbc")
    ch, ae, replay = (receipt[key] for key in ("charon_command", "aeneas_command", "replay"))
    require(ch == [parent["charon_command"][0], "cargo", "--preset=aeneas", "--sysroot=default",
                    "--dest-file=" + str(destination), "--start-from=" + SELECTOR,
                    *("--opaque=" + name for name in OPAQUE), "--", manifest,
                    "-p", "bulksketch", "--lib", "--locked", "--target", setup.TARGET]
            and ae == [parent["aeneas_command"][0], *setup.FLAGS, str(destination.parent / "stock"), str(destination)]
            and replay["command"] == [*ae[:-2], str(destination.parent / "replay"), ae[-1]]
            and replay["exit_code"] == 0
            and replay["input_sha256"] == sha(root / DIRECTORY / "arithmetic.llbc")
            and replay["log_sha256"] == sha(root / DIRECTORY / "replay.log")
            and replay["outputs"] == {name: sha(root / RAW / name) for name in
                                       ("Funs.lean", "FunsExternal_Template.lean", "Types.lean")},
            "affine splitter checked replay differs")
    llbc = json.loads((root / DIRECTORY / "arithmetic.llbc").read_text())
    translated = llbc["translated"]
    targets = translated["target_information"]
    require(llbc["has_errors"] is False and translated["options"]["start_from"] == [SELECTOR]
            and translated["options"]["opaque"] == OPAQUE and translated["options"]["dest_file"] == str(destination)
            and len(targets) == 1 and targets[0]["key"] == setup.TARGET
            and targets[0]["value"]["target_pointer_size"] == 8, "affine splitter LLBC closure or target differs")
    expected_source = {path: sha(root.parents[1] / path) for path in SOURCES}
    require(receipt["source_sha256"] == expected_source, "affine splitter pinned source differs")
    found = set()
    for fn in translated["fun_decls"]:
        if not fn:
            continue
        meta = fn["item_meta"]
        span = meta["span"]["Untagged"]["data"]
        source = translated["files"][span["file_id"]]
        file = source["name"].get("Local", "")
        if not file.startswith("src/"):
            continue
        body = fn["body"]
        kind = body if isinstance(body, str) else next(iter(body))
        if file != SOURCES[0] and kind != "Opaque":
            continue
        item = (meta["name"][-1].get("Ident", [""])[0], file, span["beg"]["line"], span["end"]["line"], kind)
        require(file in expected_source and item not in found
                and hashlib.sha256(source["contents"].encode()).hexdigest() == expected_source[file],
                "affine splitter embedded source differs")
        found.add(item)
    require(found == EXPECTED, "affine splitter body or opaque call differs")
    types = declarations(root / RAW / "Types.lean")
    require(set(types) == {name for names in SHARED.values() for name in names} | set(TYPES),
            "affine splitter type set differs")
    for path, names in SHARED.items():
        existing = declarations(root / "bridge/Arithmetic" / path)
        require(all(types[name] == existing.get(name) for name in names), "affine splitter shared type differs: " + path)
    original = declarations(root / RAW / "Funs.lean")
    shared = declarations(root / "bridge/Arithmetic/DenseNormalizationGenerated.lean")
    for name in ("core.slice.iter.Iter.Insts.CoreIterTraitsExact_sizeExactSizeIteratorSharedT",
                 "core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT"):
        require(original[name] == shared.get(name), "affine splitter iterator dictionary differs: " + name)
    require((root / ACTIVE).read_text() == projection(root), "compiled affine splitter projection differs")
    return {
        "raw_generated_file": str(RAW / "Funs.lean"), "raw_file_sha256": sha(root / RAW / "Funs.lean"),
        "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
        "source_declarations_retained_verbatim": len(TYPES) + len(FUNS),
        "shared_types_and_function_dictionary_declarations_checked": True,
        "generated_declarations": ["bulksketch." + name for name in (*TYPES, *FUNS)],
        "native_source_edited": False,
    }


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
