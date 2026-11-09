#!/usr/bin/env python3
"""Verify the exact original checked candidate-row accessor."""
from hashlib import sha256
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/candidate-row")
ACTIVE = Path("bridge/Arithmetic/CandidateRowGenerated.lean")
RAW = DIRECTORY / "Arithmetic/Funs.lean"
SELECTOR = "bulksketch::sketch::candidates::row"
NAME = "sketch.candidates.row"
MARKER = "/-- [bulksketch::sketch::candidates::row]"
CAPTURE = "28bf61542fd44ae85e000b7651dd08f0df3fde65a53c0c5bfdf14644fce99c14"
RUST = "src/sketch/candidates.rs"
SOURCE = "0a5bda53f6b07fcae8acd870e2d0c4a246d207e6"
FLAGS = ["-backend", "lean", "-checks", "-sequential", "-no-progress-bar",
         "-print-error-emitters", "-split-files", "-dest"]
FILES = {"arithmetic.llbc", "charon.log", "aeneas.log", "Arithmetic/Funs.lean",
         "Arithmetic/FunsExternal_Template.lean", "Arithmetic/Types.lean"}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return sha256(path.read_bytes()).hexdigest()


def declaration(path, name):
    body = path.read_text().split("namespace bulksketch\n", 1)[1].rsplit("end bulksketch", 1)[0]
    blocks = [item.strip() for item in re.split(r"(?m)(?=^/--)", body)
              if re.search(r"(?m)^def\s+" + re.escape(name) + r"\s", item)]
    require(len(blocks) == 1, "candidate row declaration differs: " + name)
    return blocks[0]


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    require(receipt["source_commit"] == SOURCE and receipt["selector"] == SELECTOR
            and receipt["aeneas_commit"] == "ab34bd28458a08c150b7cbf1873e59af74588138"
            and receipt["charon_commit"] == "7b462d9159db2ed3015162352183906a30bfafc6"
            and receipt["rust_toolchain"] == "nightly-2026-09-17"
            and receipt["target"] == "x86_64-apple-darwin" and receipt["checked_exit"] == 0
            and receipt["native_source_edited"] is False and receipt["binary_sha256"] == BINARIES,
            "candidate row receipt differs")
    files = receipt["files_sha256"]
    require(set(files) == {str(DIRECTORY / name) for name in FILES}, "candidate row artifact list differs")
    for path, digest in files.items():
        require(sha(root / path) == digest, "candidate row artifact differs: " + path)
    capture = root / DIRECTORY / "arithmetic.llbc"
    require(sha(capture) == CAPTURE and sha(root / RAW) == RAW_HASH, "candidate row frozen capture differs")
    embedded = [row["contents"] for row in json.loads(capture.read_bytes())["translated"]["files"]
                if row and row["name"] == {"Local": RUST}]
    require(len(embedded) == 1 and sha256(embedded[0].encode()).hexdigest() == RUST_HASH
            and receipt["source_sha256"] == {RUST: RUST_HASH}, "candidate row Rust source differs")
    ch, ae = receipt["charon_command"], receipt["aeneas_command"]
    require(ch[1:4] == ["cargo", "--preset=aeneas", "--sysroot=default"]
            and ch[5:7] == ["--start-from=" + SELECTOR, "--"]
            and ch[-6:] == ["-p", "bulksketch", "--lib", "--locked", "--target", "x86_64-apple-darwin"]
            and ae[1:-2] == FLAGS and ch[4].removeprefix("--dest-file=") == ae[-1]
            and "Generated:" in (root / DIRECTORY / "aeneas.log").read_text(),
            "candidate row stock checked commands differ")
    for path, digest in RUNTIME_HASHES.items():
        require(sha(root / path) == digest, "candidate row shared dictionary differs: " + path)
    original = declaration(root / RAW, NAME)
    header, marker, body = (root / ACTIVE).read_text().partition(MARKER)
    require(sha256(header.encode()).hexdigest() == HEADER and marker + body ==
            original + "\n\nend bulksketch\n" and "sorry" not in original, "compiled candidate row projection differs")
    return {
        "raw_generated_file": str(RAW), "raw_file_sha256": sha(root / RAW),
        "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
        "source_declarations_retained_verbatim": 1,
        "shared_types_and_function_dictionary_declarations_checked": True,
        "generated_declarations": ["bulksketch." + NAME], "native_source_edited": False,
    }


BINARIES = {'aeneas': '91f5a2776a79e2923517a2c4807c9fc017e79f185ae490502247f16e2941e330',
 'charon': '913e7969d1a0296038d115bcf1af47f8c0c6702266cc7a78a02a2b4ad7a0dfbe'}

RUST_HASH = '5071c62cae68c4cc27c3d5db00697ed4412fde698f6868a6da6e266f2e1fada5'

RUNTIME_HASHES = {'bridge/Arithmetic/Funs.lean': '4d688e3ce715126a0bf92d0c43cac8361de11c6f5215c01fdbf7caf8d3584ef9',
 'bridge/Arithmetic/MapsRuntime.lean': 'ebac090bd9b4f610659f8d8a34222e1c7be297e29f05e2ee335f1257f20bf02b'}

HEADER = '6333d58aca7f3103104a8988f8be9c58c7e7c59da678c7f7140b78c479bcc322'

RAW_HASH = 'b88864bf41e03e1bfc9f673d845653f05181b88adbf1508a461439821c0533d2'

if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
