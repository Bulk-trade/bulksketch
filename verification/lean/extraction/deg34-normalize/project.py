#!/usr/bin/env python3
"""Verify the retained original degree-normalization body and shared type boundary."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/deg34-normalize")
RAW = DIRECTORY / "Arithmetic"
ACTIVE = Path("bridge/Arithmetic/NormalizeGenerated.lean")
SELECTOR = "bulksketch::decode::deg34::normalize"
SOURCE_SHA = "50e92cc158d33b58361cf95719d4f13e01295802a15e1dab7622fab5ce050015"
SHARED = ["bridge/Arithmetic/Types.lean", "bridge/Arithmetic/SliceKernelTypes.lean"]
HEADER = """-- Exact original-source declaration projection. Imports are adapted only.
module
public import Arithmetic.SliceKernelTypes
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

"""
NAMES = ["decode.deg34.normalize_loop.body", "decode.deg34.normalize_loop",
         "decode.deg34.normalize"]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def blocks(path):
    body = path.read_text().split("namespace bulksketch\n", 1)[1].rsplit("end bulksketch", 1)[0]
    return re.findall(r"(?ms)^/--.*?(?=^/--|\Z)", body)


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    expected = {str(RAW / name) for name in ("Types.lean", "Funs.lean", "FunsExternal_Template.lean")}
    expected.update(str(DIRECTORY / name) for name in ("arithmetic.llbc", "charon.log", "aeneas.log", "replay.log"))
    artifacts = receipt["artifacts"]
    if (receipt["status"] != "generated" or receipt["llbc_has_errors"] is not False or
            len(artifacts) != len(expected) or {entry["path"] for entry in artifacts} != expected):
        raise ValueError("incomplete normalization extraction receipt")
    for entry in artifacts:
        if sha(root / entry["path"]) != entry["sha256"]:
            raise ValueError("raw normalization extraction mismatch: " + entry["path"])
    charon, checked = receipt["commands"]
    replay = receipt["pinned_checked_replay"]
    manifest = Path(charon["command"][7].removeprefix("--manifest-path="))
    input_path = Path(charon["command"][4].removeprefix("--dest-file="))
    flags = ["-backend", "lean", "-checks", "-sequential", "-no-progress-bar",
             "-print-error-emitters", "-split-files", "-dest"]
    if (receipt["source_commit"] != "0a5bda53f6b07fcae8acd870e2d0c4a246d207e6" or
            receipt["aeneas_commit"] != "ab34bd28458a08c150b7cbf1873e59af74588138" or
            receipt["charon_commit"] != "7b462d9159db2ed3015162352183906a30bfafc6" or
            receipt["tool_binary_sha256"] != {
                "aeneas": "91f5a2776a79e2923517a2c4807c9fc017e79f185ae490502247f16e2941e330",
                "charon": "913e7969d1a0296038d115bcf1af47f8c0c6702266cc7a78a02a2b4ad7a0dfbe"} or
            charon["exit_code"] != 0 or checked["exit_code"] != 0 or replay["exit_code"] != 0 or
            Path(checked["command"][0]).parts[-6:] !=
                ("tooling", "aeneas", "src", "_build", "default", "main.exe") or
            checked["command"][1:-2] != flags or Path(checked["command"][-1]) != input_path or
            replay["command"][:-2] != checked["command"][:-2] or
            Path(replay["command"][-1]) != manifest.parent / "verification/lean" / DIRECTORY / "arithmetic.llbc" or
            replay["input_sha256"] != sha(root / DIRECTORY / "arithmetic.llbc") or
            replay["log_sha256"] != sha(root / DIRECTORY / "replay.log") or
            replay["byte_identical_generated_files"] != 3 or
            replay["outputs"] != {name: sha(root / RAW / name)
                for name in ("Funs.lean", "Types.lean", "FunsExternal_Template.lean")}):
        raise ValueError("normalization checked replay linkage differs")
    source_path = Path("src/decode/deg34.rs")
    if sha(root.parents[1] / source_path) != SOURCE_SHA:
        raise ValueError("frozen normalization source differs")
    llbc = json.loads((root / DIRECTORY / "arithmetic.llbc").read_text())
    translated = llbc["translated"]
    if (llbc["has_errors"] is not False or translated["options"]["start_from"] != [SELECTOR]
            or translated["options"]["opaque"] != []):
        raise ValueError("normalization LLBC is incomplete or has a different selection")
    targets = translated["target_information"]
    if len(targets) != 1 or targets[0]["key"] != "x86_64-apple-darwin" or targets[0]["value"]["target_pointer_size"] != 8:
        raise ValueError("normalization LLBC target differs")
    name = [{"Ident": [part, 0]} for part in SELECTOR.split("::")]
    matching = [fn for fn in translated["fun_decls"] if fn and fn["item_meta"]["name"] == name]
    if len(matching) != 1 or "Structured" not in matching[0]["body"]:
        raise ValueError("original normalization body missing")
    span = matching[0]["item_meta"]["span"]["Untagged"]["data"]
    source = translated["files"][span["file_id"]]
    if (span["beg"] != {"line": 65, "col": 0} or span["end"] != {"line": 77, "col": 1}
            or source["name"] != {"Local": str(source_path)}
            or hashlib.sha256(source["contents"].encode()).hexdigest() != SOURCE_SHA):
        raise ValueError("normalization LLBC source span or contents differ")
    shared = [(root / name).read_text() for name in SHARED]
    types = blocks(root / RAW / "Types.lean")
    if len(types) != 6 or any(not any(block.strip() in file for file in shared) for block in types):
        raise ValueError("shared normalization type mismatch")
    template = (root / RAW / "FunsExternal_Template.lean").read_text()
    if re.findall(r"(?m)^axiom\s+(\S+)", template) != ["core.slice.raw.from_ref"]:
        raise ValueError("normalization external declaration set changed")
    raw = RAW / "Funs.lean"
    selected = []
    names = []
    for block in blocks(root / raw):
        name = re.search(r"(?m)^def\s+(\S+)", block)
        if name and name.group(1) in NAMES:
            selected.append(block)
            names.append(name.group(1))
    if names != NAMES or (root / ACTIVE).read_text() != HEADER + "".join(selected) + "end bulksketch\n":
        raise ValueError("compiled normalization projection differs")
    return {"raw_generated_file": str(raw), "raw_file_sha256": sha(root / raw),
            "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
            "source_declarations_retained_verbatim": len(names),
            "shared_types_and_function_dictionary_declarations_checked": True,
            "generated_declarations": ["bulksketch." + name for name in names],
            "native_source_edited": False}


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
