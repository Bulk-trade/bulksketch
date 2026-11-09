#!/usr/bin/env python3
"""Verify the frozen affine selector declarations and existing scalar bindings."""
from hashlib import sha256
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/affine-selector")
RAW = DIRECTORY / "Arithmetic"
ACTIVE = Path("bridge/Arithmetic/AffineSelectorGenerated.lean")
SHARED = Path("bridge/Arithmetic/RootSetupGenerated.lean")
SOURCE = Path("src/decode/affine.rs")
SOURCE_SHA = "a7c45498717202aec291b4c4acdd6f819edf16bcdf478500a8c74a3492c4e11d"
NAMES = ["decode.affine.square_products", "decode.affine.enumerate_preferred"]
TOOL_COMMITS = {
    "charon_commit": "7b462d9159db2ed3015162352183906a30bfafc6",
    "aeneas_commit": "ab34bd28458a08c150b7cbf1873e59af74588138",
}
TOOL_DIGESTS = {
    "charon": "913e7969d1a0296038d115bcf1af47f8c0c6702266cc7a78a02a2b4ad7a0dfbe",
    "aeneas": "91f5a2776a79e2923517a2c4807c9fc017e79f185ae490502247f16e2941e330",
}
RUST_ROOTS = [
    "bulksketch::decode::affine::enumerate_preferred",
    "bulksketch::decode::affine::square_products",
]
RUST_SPANS = {
    "enumerate_preferred": (86, 0, 95, 1),
    "square_products": (22, 0, 24, 1),
}
AENEAS_FLAGS = [
    "-backend", "lean", "-checks", "-sequential", "-no-progress-bar",
    "-print-error-emitters", "-split-files", "-dest",
]
HEADER = """-- Original stock-checked Affine selector declarations.
import Arithmetic.RootSetupGenerated
import Arithmetic.WorkScheduleRuntime
open Aeneas Aeneas.Std Result ControlFlow Error

namespace bulksketch

"""


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def body(path):
    return path.read_text().split("namespace bulksketch\n", 1)[1].rsplit("end bulksketch", 1)[0]


def declaration(text, name):
    blocks = re.findall(r"(?ms)^/--.*?(?=^/--|\Z)", text)
    matches = [block for block in blocks if re.search(r"(?m)^def " + re.escape(name) + r"\b", block)]
    if len(matches) != 1:
        raise ValueError("expected one affine selector declaration: " + name)
    return matches[0]


def check_replay(root, receipt):
    if (any(receipt[name] != commit for name, commit in TOOL_COMMITS.items()) or
            receipt["tool_binary_sha256"] != TOOL_DIGESTS or
            receipt["rust_toolchain"] != "nightly-2026-09-17" or
            receipt["target"] != "x86_64-apple-darwin" or receipt["selected_roots"] != RUST_ROOTS):
        raise ValueError("affine selector extraction tool identity differs")
    commands = receipt["commands"]
    if len(commands) != 3 or any(command["exit_code"] != 0 for command in commands):
        raise ValueError("affine selector checked extraction did not complete")
    capture, initial, replay = (command["command"] for command in commands)
    if (Path(capture[0]).name != "charon" or capture[1:4] != ["cargo", "--preset=aeneas", "--sysroot=default"] or
            [arg for arg in capture if arg.startswith("--start-from=")] != [
                "--start-from=" + name for name in RUST_ROOTS] or
            any(arg.startswith(("--opaque=", "--exclude=")) for arg in capture) or
            capture[-2:] != ["--target", "x86_64-apple-darwin"]):
        raise ValueError("affine selector Charon selector differs")
    for command, directory in ((initial, "checked"), (replay, "replay")):
        if (len(command) != 11 or Path(command[0]).name != "main.exe" or
                command[1:9] != AENEAS_FLAGS or Path(command[9]).name != directory or
                Path(command[10]).name != "arithmetic.llbc" or command[10] != initial[10]):
            raise ValueError("affine selector requires original checked extraction")
    files = {name: digest(root / RAW / name)
             for name in ("Types.lean", "Funs.lean", "FunsExternal_Template.lean")}
    if receipt["checked_replay_byte_identical"] is not True or receipt["replay_generated_sha256"] != files:
        raise ValueError("affine selector replay does not match")


def check_llbc(root):
    capture = json.loads((root / DIRECTORY / "arithmetic.llbc").read_bytes())
    if capture["has_errors"] is not False:
        raise ValueError("incomplete affine selector LLBC")
    translated = capture["translated"]
    sources = [file for file in translated["files"] if file and file["name"] == {"Local": str(SOURCE)}]
    if len(sources) != 1 or sha256(sources[0]["contents"].encode()).hexdigest() != SOURCE_SHA:
        raise ValueError("affine selector capture changed its embedded Rust source")
    for name, expected in RUST_SPANS.items():
        qualified = [{"Ident": [part, 0]} for part in ("bulksketch", "decode", "affine", name)]
        functions = [fun for fun in translated["fun_decls"] if fun and fun["item_meta"]["name"] == qualified]
        if len(functions) != 1 or set(functions[0]["body"]) != {"Structured"}:
            raise ValueError("missing structured affine selector body: " + name)
        span = functions[0]["item_meta"]["span"]["Untagged"]
        data = span["data"]
        actual = (data["beg"]["line"], data["beg"]["col"], data["end"]["line"], data["end"]["col"])
        if data["file_id"] != sources[0]["id"] or span["generated_from_span"] is not None or actual != expected:
            raise ValueError("affine selector body span differs: " + name)


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    artifacts = receipt["artifacts"]
    expected = {str(RAW / name) for name in ("Types.lean", "Funs.lean", "FunsExternal_Template.lean")}
    expected.update(str(DIRECTORY / name) for name in ("arithmetic.llbc", "charon.log", "aeneas.log", "replay.log"))
    if (receipt["status"] != "generated" or receipt["llbc_has_errors"] is not False or
            receipt["native_source_edited"] is not False or len(artifacts) != len(expected) or
            {item["path"] for item in artifacts} != expected):
        raise ValueError("incomplete affine selector extraction receipt")
    for item in artifacts:
        if digest(root / item["path"]) != item["sha256"]:
            raise ValueError("affine selector extraction mismatch: " + item["path"])
    if digest(root.parents[1] / SOURCE) != SOURCE_SHA or receipt["source_sha256"] != {str(SOURCE): SOURCE_SHA}:
        raise ValueError("frozen affine selector source differs")
    check_replay(root, receipt)
    check_llbc(root)
    if body(root / RAW / "Types.lean").strip():
        raise ValueError("affine selector capture gained local types")
    externals = re.findall(r"(?m)^axiom\s+(\S+)", (root / RAW / "FunsExternal_Template.lean").read_text())
    if externals != ["core.num.U64.checked_shl", "core.num.U64.div_ceil"]:
        raise ValueError("affine selector scalar binding set changed")
    raw = RAW / "Funs.lean"
    selected = body(root / raw).lstrip("\n")
    if re.findall(r"(?m)^def\s+(\S+)", selected) != NAMES:
        raise ValueError("affine selector declaration set changed")
    if declaration(selected, NAMES[0]) != declaration(body(root / SHARED), NAMES[0]):
        raise ValueError("shared square_products differs from the checked affine selector capture")
    if (root / ACTIVE).read_text() != HEADER + declaration(selected, NAMES[1]) + "end bulksketch\n":
        raise ValueError("compiled affine selector projection differs")
    return {"raw_generated_file": str(raw), "raw_file_sha256": digest(root / raw),
            "compiled_projection": str(ACTIVE), "projection_file_sha256": digest(root / ACTIVE),
            "source_declarations_retained_verbatim": 1,
            "generated_declarations": ["bulksketch." + NAMES[1]],
            "shared_compiled_projection": str(SHARED),
            "shared_projection_file_sha256": digest(root / SHARED),
            "shared_generated_declarations": ["bulksketch." + NAMES[0]],
            "shared_types_and_function_dictionary_declarations_checked": True,
            "native_source_edited": False}


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
