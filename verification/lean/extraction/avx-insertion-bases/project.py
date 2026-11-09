#!/usr/bin/env python3
"""Verify the original stock AVX insertion-bases generator projection."""
import hashlib
import importlib.util
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
SQUARE = importlib.util.spec_from_file_location("avx_square", ROOT / "extraction/avx-square/project.py")
square = importlib.util.module_from_spec(SQUARE)
SQUARE.loader.exec_module(square)
require, sha, declarations = square.require, square.sha, square.declarations
DIRECTORY = Path("extraction/avx-insertion-bases")
RAW = DIRECTORY / "Arithmetic"
ACTIVE = Path("bridge/Arithmetic/AvxInsertionBasesGenerated.lean")
SOURCE = "src/backend/x86_vpclmul512.rs"
FIELD = "src/field/frobenius.rs"
SELECTOR = "bulksketch::backend::x86_vpclmul512::insertion_bases"
OPAQUE = ["bulksketch::field::frobenius::square"]
PREFIX = "backend.x86_vpclmul512.insertion_bases"
NAMES = tuple(PREFIX + suffix for suffix in ("_loop0_loop0_loop0.body", "_loop0_loop0_loop0",
    "_loop0_loop0.body", "_loop0_loop0", "_loop0.body", "_loop0", ""))
OUTPUTS = ("Funs.lean", "FunsExternal_Template.lean", "Types.lean")
ARTIFACTS = {str(RAW / name) for name in OUTPUTS} | {
    str(DIRECTORY / name) for name in ("arithmetic.llbc", "charon.log", "aeneas.log", "replay.log")
}
HEADER = """-- The seven original generator declarations from checked stock extraction.
import Arithmetic.AvxSingleBasesGenerated
import Arithmetic.FrobeniusConstGenerated

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace bulksketch

"""


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    parent = json.loads((root / "extraction/avx-square/receipt.json").read_text())
    require(all(receipt[key] == parent[key] for key in ("source_commit", "rust_toolchain", "target",
                "charon_commit", "aeneas_commit", "tool_binary_sha256", "native_source_edited"))
            and receipt["selector"] == SELECTOR and receipt["opaque_application_bodies"] == OPAQUE
            and set(receipt["source_sha256"]) == {SOURCE, FIELD}
            and receipt["source_sha256"][SOURCE] == parent["source_sha256"][SOURCE]
            and set(receipt["artifacts"]) == ARTIFACTS, "invalid insertion-bases generator receipt")
    for path, digest in receipt["artifacts"].items():
        require(sha(root / path) == digest, "insertion-bases generator artifact differs: " + path)
    require(receipt["source_sha256"] == {path: sha(root.parents[1] / path) for path in (SOURCE, FIELD)},
            "insertion-bases generator frozen Rust source differs")
    prior = parent["commands"]["charon"]["command"]
    manifest = next(arg for arg in prior if arg.startswith("--manifest-path="))
    folder = Path(manifest.removeprefix("--manifest-path=")).parent.parent / "bulksketch-proof-evidence-20261109-avx-encode18/bases-generator"
    capture = str(folder / "arithmetic.llbc")
    commands = receipt["commands"]
    require(set(commands) == {"charon", "aeneas", "replay"}
            and all(value["exit_code"] == 0 for value in commands.values()), "insertion-bases generator capture failed")
    require(commands["charon"]["command"] == [*prior[:4], "--dest-file=" + capture, "--start-from=" + SELECTOR,
            *("--opaque=" + name for name in OPAQUE), "--", manifest, "-p", "bulksketch", "--lib",
            "--locked", "--offline", "--target", square.TARGET], "insertion-bases generator capture command differs")
    for name, output in (("aeneas", "stock"), ("replay", "replay")):
        require(commands[name]["command"] == [parent["commands"]["aeneas"]["command"][0], *square.FLAGS,
                str(folder / output), capture], "insertion-bases generator checked command differs")
    require(receipt["replayed_outputs"] == {name: sha(root / RAW / name) for name in OUTPUTS},
            "insertion-bases generator replay differs")
    llbc = json.loads((root / DIRECTORY / "arithmetic.llbc").read_text())
    crate = llbc["translated"]
    opts, targets = crate["options"], crate["target_information"]
    require(llbc["has_errors"] is False and opts["start_from"] == [SELECTOR] and opts["opaque"] == OPAQUE
            and opts["dest_file"] == capture and opts["skip_borrowck"] is False and len(targets) == 1
            and targets[0]["key"] == square.TARGET and targets[0]["value"]["target_pointer_size"] == 8,
            "insertion-bases generator original LLBC scope differs")
    found = set()
    for fn in crate["fun_decls"]:
        if not fn:
            continue
        meta = fn["item_meta"]
        span = meta["span"]["Untagged"]["data"]
        file = crate["files"][span["file_id"]]
        path = file["name"].get("Local", "")
        if not path.startswith("src/"):
            continue
        require(path in receipt["source_sha256"]
                and hashlib.sha256(file["contents"].encode()).hexdigest() == receipt["source_sha256"][path],
                "insertion-bases generator embedded Rust source differs")
        body = fn["body"]
        found.add((meta["name"][-1].get("Ident", [""])[0], path, span["beg"]["line"], span["end"]["line"],
                   body if isinstance(body, str) else next(iter(body))))
    require(found == {("insertion_bases", SOURCE, 486, 518, "Structured"),
                      ("square", FIELD, 55, 77, "Opaque")}, "insertion-bases generator source closure differs")
    original = (root / RAW / "Funs.lean").read_text()
    marker = "/-- [" + SELECTOR + "]: loop body 2:"
    suffix = original[original.index(marker):]
    require(tuple(re.findall(r"(?m)^def (backend\.x86_vpclmul512\.insertion_bases\S*)", suffix)) == NAMES
            and (root / ACTIVE).read_text() == HEADER + suffix, "compiled insertion-bases generator projection differs")
    require(declarations(root / RAW / "Types.lean") ==
            declarations(root / "extraction/avx-single-bases/Arithmetic/Types.lean"),
            "insertion-bases generator shared table type differs")
    square_source = declarations(root / "extraction/frobenius-const/square/Arithmetic/Funs.lean")
    square_active = declarations(root / "bridge/Arithmetic/FrobeniusConstGenerated.lean")
    require(all(square_active.get(name) == body for name, body in square_source.items()
                if name.startswith("field.frobenius.square")), "insertion-bases generator imported square differs")
    return {"raw_generated_file": str(RAW / "Funs.lean"), "raw_file_sha256": sha(root / RAW / "Funs.lean"),
        "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
        "source_declarations_retained_verbatim": len(NAMES),
        "shared_types_and_function_dictionary_declarations_checked": True,
        "generated_declarations": ["bulksketch." + name for name in NAMES], "native_source_edited": False}


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
