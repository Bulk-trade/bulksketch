#!/usr/bin/env python3
"""Verify the stock checked original AVX immutable insertion table initializer."""
import hashlib
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
GENERATOR = importlib.util.spec_from_file_location("avx_insertion_bases", ROOT / "extraction/avx-insertion-bases/project.py")
generator = importlib.util.module_from_spec(GENERATOR)
GENERATOR.loader.exec_module(generator)
require, sha, declarations = generator.require, generator.sha, generator.declarations
DIRECTORY = Path("extraction/avx-insertion-bases-static")
RAW = DIRECTORY / "Arithmetic"
ACTIVE = Path("bridge/Arithmetic/AvxInsertionBasesStaticGenerated.lean")
SOURCE = "src/backend/x86_vpclmul512.rs"
FIELD = "src/field/frobenius.rs"
SELECTOR = "bulksketch::backend::x86_vpclmul512::INSERT_BASES"
NAME = "backend.x86_vpclmul512.INSERT_BASES"
OPAQUE = ["bulksketch::field::frobenius::square"]
MARKER = "/-- [" + SELECTOR + "]"
GENERATOR_MARKER = "/-- [bulksketch::backend::x86_vpclmul512::insertion_bases]: loop body 2:"
OUTPUTS = ("Funs.lean", "FunsExternal_Template.lean", "Types.lean")
ARTIFACTS = {str(RAW / name) for name in OUTPUTS} | {
    str(DIRECTORY / name) for name in ("arithmetic.llbc", "charon.log", "aeneas.log", "replay.log")
}
HEADER = """-- Exact original immutable static initializer declaration from stock checked extraction.
import Arithmetic.AvxInsertionBasesGenerated

open Aeneas Aeneas.Std Result
set_option linter.dupNamespace false

namespace bulksketch

"""


def calls(value):
    if isinstance(value, dict):
        if "Call" in value:
            yield value["Call"]
        for item in value.values():
            yield from calls(item)
    elif isinstance(value, list):
        for item in value:
            yield from calls(item)


def source_span(crate, meta, path, expected_hash):
    span = meta["span"]["Untagged"]["data"]
    file = crate["files"][span["file_id"]]
    require(file["name"] == {"Local": path} and hashlib.sha256(file["contents"].encode()).hexdigest() == expected_hash,
            "insertion static embedded source differs")
    return (span["beg"]["line"], span["end"]["line"])


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    prior = json.loads((root / generator.DIRECTORY / "receipt.json").read_text())
    require(all(receipt[key] == prior[key] for key in ("source_commit", "target", "rust_toolchain", "charon_commit",
                "aeneas_commit", "tool_binary_sha256", "native_source_edited", "source_sha256"))
            and receipt["selector"] == SELECTOR and receipt["opaque_application_bodies"] == OPAQUE
            and set(receipt["artifacts"]) == ARTIFACTS, "invalid insertion static receipt")
    for path, digest in receipt["artifacts"].items():
        require(sha(root / path) == digest, "insertion static artifact differs: " + path)
    require(receipt["source_sha256"] == {path: sha(root.parents[1] / path) for path in (SOURCE, FIELD)},
            "insertion static frozen Rust source differs")
    commands = receipt["commands"]
    require(set(commands) == {"charon", "aeneas", "replay"}
            and all(entry["exit_code"] == 0 for entry in commands.values()), "insertion static checked capture failed")
    prior_charon = prior["commands"]["charon"]["command"]
    manifest = next(word for word in prior_charon if word.startswith("--manifest-path="))
    folder = Path(manifest.removeprefix("--manifest-path=")).parent.parent / (
        "bulksketch-proof-evidence-20261109-avx-encode18/bases-static")
    capture = str(folder / "arithmetic.llbc")
    require(commands["charon"]["command"] == [
        *prior_charon[:4], "--dest-file=" + capture, "--start-from=" + SELECTOR,
        *("--opaque=" + name for name in OPAQUE), "--", manifest, "-p", "bulksketch", "--lib",
        "--locked", "--offline", "--target", generator.square.TARGET,
    ], "insertion static original Charon command differs")
    for key, output in (("aeneas", "stock"), ("replay", "replay")):
        require(commands[key]["command"] == [prior["commands"]["aeneas"]["command"][0],
            *generator.square.FLAGS, str(folder / output), capture], "insertion static checked command differs")
    require(receipt["replayed_outputs"] == {name: sha(root / RAW / name) for name in OUTPUTS},
            "insertion static replay output differs")
    llbc = json.loads((root / DIRECTORY / "arithmetic.llbc").read_text())
    crate = llbc["translated"]
    opts, targets = crate["options"], crate["target_information"]
    require(llbc["has_errors"] is False and opts["start_from"] == [SELECTOR] and opts["opaque"] == OPAQUE
            and opts["dest_file"] == capture and opts["skip_borrowck"] is False and len(targets) == 1
            and targets[0]["key"] == generator.square.TARGET and targets[0]["value"]["target_pointer_size"] == 8,
            "insertion static original LLBC scope differs")
    globals_ = [g for g in crate["global_decls"] if g and g["item_meta"]["name"][-1].get("Ident", [""])[0] == "INSERT_BASES"]
    require(len(globals_) == 1, "insertion static original declaration missing")
    static = globals_[0]
    require(static["item_meta"]["opacity"] == "Transparent"
            and source_span(crate, static["item_meta"], SOURCE, receipt["source_sha256"][SOURCE]) == (519, 519)
            and static["global_kind"] == {"Static": {"is_mut": False, "is_safe": True, "is_thread_local": False}},
            "insertion static original definition differs")
    functions = {}
    expected = {
        "INSERT_BASES": (SOURCE, (519, 519), "Structured"),
        "insertion_bases": (SOURCE, (486, 518), "Structured"),
        "square": (FIELD, (55, 77), "Opaque"),
    }
    for fn in crate["fun_decls"]:
        if not fn:
            continue
        meta = fn["item_meta"]
        span = meta["span"]["Untagged"]["data"]
        path = crate["files"][span["file_id"]]["name"].get("Local", "")
        if not path.startswith("src/"):
            continue
        name = meta["name"][-1].get("Ident", [""])[0]
        require(name in expected and name not in functions, "insertion static native declaration set differs")
        expected_path, expected_span, kind = expected[name]
        body = fn["body"]
        require(expected_path == path and source_span(crate, meta, path, receipt["source_sha256"][path]) == expected_span
                and (body if isinstance(body, str) else next(iter(body))) == kind,
                "insertion static native declaration differs: " + name)
        functions[name] = fn
    require(set(functions) == set(expected), "insertion static source closure differs")
    global_call = list(calls(static["value"]))
    require(len(global_call) == 1 and global_call[0][0]["kind"] == {"Fun": functions["INSERT_BASES"]["def_id"]}
            and global_call[0][1] == [], "insertion static global initializer differs")
    call = list(calls(functions["INSERT_BASES"]["body"]))
    require(len(call) == 1 and call[0]["call"]["func"]["Regular"]["kind"] == {"Fun": functions["insertion_bases"]["def_id"]}
            and call[0]["call"]["args"] == [], "insertion static actual generator call differs")
    raw = (root / RAW / "Funs.lean").read_text()
    prior_raw = (root / generator.RAW / "Funs.lean").read_text()
    require(raw[raw.index(GENERATOR_MARKER):raw.index(MARKER)] ==
            prior_raw[prior_raw.index(GENERATOR_MARKER):prior_raw.rindex("end bulksketch")],
            "insertion static original imported generator differs")
    require(declarations(root / RAW / "Types.lean") == declarations(root / generator.RAW / "Types.lean"),
            "insertion static table type differs")
    require((root / ACTIVE).read_text() == HEADER + raw[raw.index(MARKER):],
            "compiled insertion static projection differs")
    return {"raw_generated_file": str(RAW / "Funs.lean"), "raw_file_sha256": sha(root / RAW / "Funs.lean"),
        "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
        "source_declarations_retained_verbatim": 1,
        "shared_types_and_function_dictionary_declarations_checked": True,
        "generated_declarations": ["bulksketch." + NAME], "native_source_edited": False}


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
