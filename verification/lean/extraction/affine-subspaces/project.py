#!/usr/bin/env python3
"""Check the stock Aeneas projection of the original affine subspace table."""
import hashlib
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SETUP = importlib.util.spec_from_file_location("root_setup", ROOT / "extraction/root-setup/project.py")
setup = importlib.util.module_from_spec(SETUP)
SETUP.loader.exec_module(setup)
require, sha, declarations = setup.require, setup.sha, setup.declarations

DIRECTORY = Path("extraction/affine-subspaces")
RAW = DIRECTORY / "Arithmetic"
ACTIVE = Path("bridge/Arithmetic/AffineSubspacesGenerated.lean")
NAME = "decode.affine.subspaces"
SELECTOR = "bulksketch::decode::affine::subspaces"
OPAQUE = ["bulksketch::decode::affine::linear_eval"]
START = "decode.affine.subspace_start"
FUNS = (START,) + tuple(NAME + suffix for suffix in ("_loop0_loop0.body", "_loop0_loop0", "_loop0.body", "_loop0", ""))
GENERATED_FILES = ("Funs.lean", "FunsExternal_Template.lean", "Types.lean")
ARTIFACTS = {str(DIRECTORY / name) for name in ("arithmetic.llbc", "charon.log", "aeneas.log", "replay.log")}
ARTIFACTS |= {str(RAW / name) for name in GENERATED_FILES}
SOURCE = "src/decode/affine.rs"
SOURCE_SHA256 = "a7c45498717202aec291b4c4acdd6f819edf16bcdf478500a8c74a3492c4e11d"
EXPECTED = {
    ("subspaces", 251, 266, "Structured"),
    ("subspace_start", 245, 247, "Structured"),
    ("linear_eval", 234, 243, "Opaque"),
}
SHARED = {
    "Types.lean": {"types.RawProduct", "types.FieldId", "field.sealed.Sealed", "field.BinaryField"},
    "SliceKernelTypes.lean": {"backend.contract.Arithmetic", "backend.contract.BulkKernels"},
}
EVAL = "decode.affine.linear_eval"
HEADER = """-- Exact checked source projection. See extraction/affine-subspaces for provenance.
-- The shared triangular offset and both table loops are original stock declarations.
import Arithmetic.AffineLinearEvalGenerated

open Aeneas Aeneas.Std Result ControlFlow Error

namespace bulksketch

set_option linter.dupNamespace false
set_option linter.unusedVariables false

"""


def projection(root=ROOT):
    functions = declarations(root / RAW / "Funs.lean")
    return HEADER + "\n\n".join(functions[name] for name in FUNS) + "\n\nend bulksketch\n"


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    require(receipt["source_commit"] == setup.SOURCE and receipt["selector"] == SELECTOR
            and receipt["target"] == setup.TARGET and receipt["rust_toolchain"] == "nightly-2026-09-17"
            and receipt["aeneas_commit"] == setup.AENEAS and receipt["charon_commit"] == setup.CHARON
            and receipt["binary_sha256"] == setup.BINARY_SHA256 and receipt["native_source_edited"] is False
            and receipt["opaque_application_bodies"] == OPAQUE and receipt["checked_exit"] == 0
            and receipt["source_sha256"] == {SOURCE: SOURCE_SHA256}
            and set(receipt["files_sha256"]) == ARTIFACTS, "invalid affine subspaces receipt")
    for path, expected in receipt["files_sha256"].items():
        require(sha(root / path) == expected, "affine subspaces artifact differs: " + path)

    parent = json.loads((root / "extraction/root-setup/receipt.json").read_text())
    manifest = next(word for word in parent["charon_command"] if word.startswith("--manifest-path="))
    destination = Path(manifest.removeprefix("--manifest-path=")).parent.parent / (
        "bulksketch-proof-evidence-20261109-native-root-run/affine-subspaces/arithmetic.llbc")
    ch, ae, replay = (receipt[key] for key in ("charon_command", "aeneas_command", "replay"))
    require(ch == [parent["charon_command"][0], "cargo", "--preset=aeneas", "--sysroot=default",
                   "--dest-file=" + str(destination), "--start-from=" + SELECTOR,
                   *("--opaque=" + name for name in OPAQUE), "--", manifest,
                   "-p", "bulksketch", "--lib", "--locked", "--target", setup.TARGET]
            and ae == [parent["aeneas_command"][0], *setup.FLAGS, str(destination.parent / "stock"), str(destination)]
            and replay["command"] == [*ae[:-2], str(destination.parent / "stock-replay"), ae[-1]]
            and replay["exit_code"] == 0
            and replay["input_sha256"] == sha(root / DIRECTORY / "arithmetic.llbc")
            and replay["log_sha256"] == sha(root / DIRECTORY / "replay.log")
            and replay["outputs"] == {name: sha(root / RAW / name) for name in GENERATED_FILES},
            "affine subspaces checked replay differs")

    llbc = json.loads((root / DIRECTORY / "arithmetic.llbc").read_text())
    translated = llbc["translated"]
    options, targets = translated["options"], translated["target_information"]
    require(llbc["has_errors"] is False and options["start_from"] == [SELECTOR]
            and options["opaque"] == OPAQUE and options["dest_file"] == str(destination)
            and len(targets) == 1 and targets[0]["key"] == setup.TARGET
            and targets[0]["value"]["target_pointer_size"] == 8, "affine subspaces LLBC closure or target differs")
    require(sha(root.parents[1] / SOURCE) == SOURCE_SHA256, "affine subspaces pinned Rust source differs")
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
        if file != SOURCE and kind != "Opaque":
            continue
        item = (meta["name"][-1].get("Ident", [""])[0], span["beg"]["line"], span["end"]["line"], kind)
        require(file == SOURCE and item not in found
                and hashlib.sha256(source["contents"].encode()).hexdigest() == SOURCE_SHA256,
                "affine subspaces embedded source differs")
        found.add(item)
    require(found == EXPECTED, "affine subspaces source body or opaque call differs")

    types = declarations(root / RAW / "Types.lean")
    require(set(types) == {name for names in SHARED.values() for name in names}, "affine subspaces type set differs")
    for path, names in SHARED.items():
        existing = declarations(root / "bridge/Arithmetic" / path)
        require(all(types[name] == existing.get(name) for name in names), "affine subspaces shared type differs: " + path)
    linear_eval = declarations(root / "bridge/Arithmetic/AffineLinearEvalGenerated.lean")
    original_eval = declarations(root / "extraction/affine-linear-eval/Arithmetic/Funs.lean")
    require(all(linear_eval.get(name) == original_eval[name] for name in (EVAL, EVAL + "_loop", EVAL + "_loop.body")),
            "affine subspaces imported linear_eval differs")
    require((root / ACTIVE).read_text() == projection(root), "compiled affine subspaces projection differs")
    return {
        "raw_generated_file": str(RAW / "Funs.lean"), "raw_file_sha256": sha(root / RAW / "Funs.lean"),
        "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
        "source_declarations_retained_verbatim": len(FUNS),
        "shared_types_and_function_dictionary_declarations_checked": True,
        "generated_declarations": ["bulksketch." + name for name in FUNS],
        "native_source_edited": False,
    }


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
