#!/usr/bin/env python3
"""Check the original AVX sparse insert and exact generated projection."""
from hashlib import sha256
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/avx-sparse-insert")
ACTIVE = Path("bridge/Arithmetic/AvxSparseInsertGenerated.lean")
RAW = DIRECTORY / "Arithmetic/Funs.lean"
SOURCE = "src/backend/x86_vpclmul512.rs"
MARKER = "/-- [bulksketch::backend::x86_vpclmul512::insert_sparse]"
SELECTOR = "bulksketch::backend::x86_vpclmul512::insert_sparse"
FLAGS = ["-backend", "lean", "-checks", "-sequential", "-no-progress-bar", "-print-error-emitters", "-split-files", "-dest"]
FILES = {str(DIRECTORY / name) for name in (
    "arithmetic.llbc", "charon.log", "aeneas.log", "replay.log",
    "Arithmetic/Funs.lean", "Arithmetic/Types.lean", "Arithmetic/FunsExternal_Template.lean",
)}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return sha256(path.read_bytes()).hexdigest()


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    parent = json.loads((root / "extraction/avx-recurrence/receipt.json").read_text())
    require(all(receipt[key] == parent[key] for key in ("source_commit", "rust_toolchain",
        "target", "aeneas_commit", "charon_commit", "tool_binary_sha256"))
        and receipt["native_source_edited"] is False, "invalid AVX sparse insert receipt")
    require(set(receipt["artifacts"]) == FILES, "incomplete AVX sparse insert receipt")
    for file, digest in receipt["artifacts"].items():
        require(sha(root / file) == digest, "AVX sparse insert artifact differs: " + file)
    require(sha(root / DIRECTORY / "arithmetic.llbc") ==
            "2326c33be53d19b1b2da656ee70cbefe2550c8ecc59be3d3229c2dba6a12ecc3",
            "original AVX sparse insert capture differs")
    require(sha(root / RAW) == "dc5c9abef7442af1a823cb26a404b6a83402350ec86a97c02a83fd4a024cacba",
            "original AVX sparse insert generated output differs")
    capture = json.loads((root / DIRECTORY / "arithmetic.llbc").read_text())
    crate = capture["translated"]
    opts = crate["options"]
    require(capture["has_errors"] is False and opts["skip_borrowck"] is False
            and opts["start_from"] == [SELECTOR] and opts["include"] == []
            and opts["opaque"] == ["bulksketch::backend::x86_vpclmul512::insert"], "AVX sparse insert capture differs")
    expected_sources = {SOURCE}
    require(set(receipt["source_sha256"]) == expected_sources, "incomplete AVX sparse insert Rust sources")
    for source, digest in receipt["source_sha256"].items():
        matches = [file["contents"] for file in crate["files"] if file and file["name"] == {"Local": source}]
        require(len(matches) == 1 and sha256(matches[0].encode()).hexdigest() == digest
                and sha(root.parents[1] / source) == digest, "AVX sparse insert Rust source differs: " + source)
    decls = {}
    for fn in crate["fun_decls"]:
        if fn and fn["item_meta"]["name"][-1].get("Ident", [""])[0] in {"insert_sparse", "insert"}:
            span = fn["item_meta"]["span"]["Untagged"]["data"]
            if crate["files"][span["file_id"]]["name"] == {"Local": SOURCE}:
                decls[span["beg"]["line"]] = (span["end"]["line"], fn["body"])
    require(set(decls) == {431, 396} and decls[431][0] == 435 and "Structured" in decls[431][1]
            and decls[396] == (425, "Opaque"),
            "AVX sparse insert original source body differs")
    ch, ae = (receipt["commands"][name] for name in ("charon", "aeneas"))
    replay = receipt["replay"]
    require(ch["exit_code"] == ae["exit_code"] == replay["exit_code"] == 0
            and ch["command"][4].removeprefix("--dest-file=") == ae["command"][-1] == replay["command"][-1]
            and ch["command"][-2:] == ["--target", receipt["target"]]
            and f"--start-from={SELECTOR}" in ch["command"]
            and [arg.removeprefix("--opaque=") for arg in ch["command"] if arg.startswith("--opaque=")] == opts["opaque"]
            and ae["command"][1:-2] == replay["command"][1:-2] == FLAGS
            and replay["identical_outputs"] is True
            and replay["outputs_sha256"] == {name: sha(root / DIRECTORY / "Arithmetic" / name)
                for name in ("Funs.lean", "Types.lean", "FunsExternal_Template.lean")},
            "AVX sparse insert checked replay differs")
    require(set(receipt["shared_sha256"]) == SHARED, "incomplete AVX sparse insert runtime link")
    for file, digest in receipt["shared_sha256"].items():
        require(sha(root / file) == digest, "AVX sparse insert shared declaration differs: " + file)
    raw = (root / RAW).read_text()
    body = raw[raw.index(MARKER):]
    require(body.count(MARKER) == 3, "AVX sparse insert projected declaration count differs")
    external = (root / DIRECTORY / "Arithmetic/FunsExternal_Template.lean").read_text()
    require("axiom backend.x86_vpclmul512.insert : Slice Std.U64 → Slice Std.U64 → Result (Slice Std.U64)" in
            " ".join(external.split()), "AVX sparse insert callee signature differs")
    for name, suffix in (("insert_sparse_loop.body", ": loop 0:"), ("insert_sparse_loop", ":\n")):
        symbol = "backend.x86_vpclmul512." + name
        anchor = MARKER + suffix
        body = body.replace(anchor, f'local notation "{symbol}" => ({symbol} insertModel)\n\n' + anchor, 1)
    require((root / ACTIVE).read_text() == HEADER + body, "compiled AVX sparse insert projection differs")
    return {"raw_generated_file": str(RAW), "raw_file_sha256": sha(root / RAW),
            "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
            "source_declarations_retained_verbatim": 3,
            "generated_declarations": ["bulksketch.backend.x86_vpclmul512." + name for name in ("insert_sparse_loop.body", "insert_sparse_loop", "insert_sparse")],
            "shared_types_and_function_dictionary_declarations_checked": True,
            "native_source_edited": False}


HEADER = '-- Original checked sparse insertion with its recursive insert callee bound explicitly.\nimport Arithmetic.AvxInsertDispatchGenerated\n\nopen Aeneas Aeneas.Std Result ControlFlow Error\n\nnamespace bulksketch\n\nvariable (insertModel : AvxInsertDispatchRuntime.Batch)\nlocal notation "backend.x86_vpclmul512.insert" => insertModel\n\n'
SHARED = {"bridge/Arithmetic/AvxInsertDispatchGenerated.lean"}

if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
