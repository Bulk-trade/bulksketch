#!/usr/bin/env python3
"""Bind the original stock checked report extraction to its compiled declarations."""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/decode-report")
ACTIVE = Path("bridge/Arithmetic/DecodeReportGenerated.lean")
SOURCE = Path("src/sketch/api.rs")
SOURCE_COMMIT = "0a5bda53f6b07fcae8acd870e2d0c4a246d207e6"
CHARON_COMMIT = "7b462d9159db2ed3015162352183906a30bfafc6"
AENEAS_COMMIT = "ab34bd28458a08c150b7cbf1873e59af74588138"
ACTIVE_SHA = "28f4fbc2573386934dca334f948efa4cd9d2efa8865db673e0795ae9d8770218"
LLBC_SHA = "050cf6b45a56cb00e4a323b93e68c656e664264be92e184c391e5f772030a0dd"
RAW_SHA = "2da248903638770ce232e3661728b16431a0bc4741efd03c6c5ab7c63f4de656"
API = "bulksketch::sketch::api::_::"
SELECTORS = [API + name for name in ("outcome", "bucket_count")]
OPAQUE = [API + name for name in ("new", "write", "fail", "finish")]
FLAGS = ["-backend", "lean", "-checks", "-sequential", "-no-progress-bar",
         "-print-error-emitters", "-split-files", "-dest"]
MARKER = "/-- [bulksketch::sketch::api::{bulksketch::sketch::api::DecodeReport<"
DECLARATIONS = ["sketch.api.DecodeReport.bucket_count", "sketch.api.DecodeReport.outcome"]
FILES = {"Types.lean", "FunsExternal_Template.lean", "Funs.lean"}
TYPE_MODULES = {
    "Arithmetic/ReconstructionTypes": ("types.DecodeFailure",),
    "Workmeter/Types": ("types.WorkUnits",),
    "Arithmetic/PublicationFrameGenerated": (
        "sketch.api.OutcomeStatus", "sketch.api.StoredOutcome", "sketch.api.DecodeReport",
    ),
    "Arithmetic/PublicationWriteGenerated": ("sketch.api.DecodeOutcome",),
}
RUNTIME_MODULES = ("MapsRuntime", "ShapeWireRuntime")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def type_declaration(path, name):
    match = re.search(
        r"(?m)^((?:@\[[^\n]+\]\n)*(?:def|structure|inductive) "
        + re.escape(name) + r"(?: where| :=)[\s\S]*?)(?=\n\n)",
        path.read_text(),
    )
    require(match is not None, f"Missing declaration {name} in {path}")
    return match[1]


def check(root=ROOT, source_root=None, dependencies=None):
    source_root = source_root or root.parents[1]
    dependencies = dependencies or root
    directory = root / DIRECTORY
    receipt = json.loads((directory / "receipt.json").read_text())
    require(receipt["source_commit"] == SOURCE_COMMIT
            and receipt["charon_commit"] == CHARON_COMMIT
            and receipt["aeneas_commit"] == AENEAS_COMMIT
            and receipt["rust_toolchain"] == "nightly-2026-09-17"
            and receipt["target"] == "x86_64-apple-darwin"
            and receipt["native_source_edited"] is False
            and receipt["native_llbc_edited"] is False,
            "Invalid stock report receipt")
    for relative, expected in receipt["artifacts"].items():
        require(sha(root / relative) == expected, f"Captured report artifact differs: {relative}")
    runtime = {f"bridge/Arithmetic/{module}.lean": sha(
        dependencies / f"bridge/Arithmetic/{module}.lean") for module in RUNTIME_MODULES}
    require(receipt["runtime_sha256"] == runtime, "Report runtime binding differs")
    llbc_path = directory / "arithmetic.llbc"
    require(sha(llbc_path) == LLBC_SHA, "Original report LLBC differs")
    capture = json.loads(llbc_path.read_bytes())
    crate = capture["translated"]
    options = crate["options"]
    require(capture["has_errors"] is False and options["skip_borrowck"] is False
            and options["start_from"] == options["include"] == SELECTORS
            and options["opaque"] == OPAQUE, "Report capture scope differs")
    source = source_root / SOURCE
    files = [item for item in crate["files"] if item and item["name"] == {"Local": str(SOURCE)}]
    require(len(files) == 1 and files[0]["contents"].encode() == source.read_bytes()
            and receipt["source_sha256"] == {str(SOURCE): sha(source)},
            "Frozen report Rust source differs")
    ch, ae, replay = receipt["commands"]["charon"], receipt["commands"]["aeneas"], receipt["replay"]
    require(ch["exit_code"] == ae["exit_code"] == replay["exit_code"] == 0
            and ch["command"][1:4] == ["cargo", "--preset=aeneas", "--sysroot=default"]
            and ch["command"][5:13] == [*(f"--start-from={name}" for name in SELECTORS),
                                      *(f"--include={name}" for name in SELECTORS),
                                      *(f"--opaque={name}" for name in OPAQUE)]
            and ch["command"][-7:] == ["-p", "bulksketch", "--lib", "--locked", "--offline",
                                        "--target", "x86_64-apple-darwin"]
            and ae["command"][1:-2] == replay["command"][1:-2] == FLAGS
            and ch["command"][4].removeprefix("--dest-file=") == ae["command"][-1] == replay["command"][-1],
            "Checked report commands differ")
    generated = directory / "Arithmetic"
    output_sha = {path.name: sha(path) for path in generated.glob("*.lean")}
    require(set(output_sha) == FILES and replay["output_sha256"] == output_sha,
            "Stock report replay differs")
    for module, names in TYPE_MODULES.items():
        for name in names:
            require(type_declaration(generated / "Types.lean", name)
                    == type_declaration(dependencies / f"bridge/{module}.lean", name),
                    f"Report declaration {name} differs")
    raw_path = generated / "Funs.lean"
    active_path = root / ACTIVE
    require(sha(raw_path) == RAW_SHA and sha(active_path) == ACTIVE_SHA,
            "Compiled report projection differs")
    raw_text, active_text = raw_path.read_text(), active_path.read_text()
    position = lambda text: text.index(MARKER)
    require(raw_text.count(MARKER) == active_text.count(MARKER) == len(DECLARATIONS)
            and active_text[position(active_text):] == raw_text[position(raw_text):],
            "Checked report declarations are not verbatim")
    names = re.findall(r"(?m)^def\s+(sketch\.api\.DecodeReport\.[^\s]+)", active_text)
    require(names == DECLARATIONS, "Report declaration inventory differs")
    return {"raw_generated_file": str(DIRECTORY / "Arithmetic/Funs.lean"),
            "raw_file_sha256": RAW_SHA, "compiled_projection": str(ACTIVE),
            "projection_file_sha256": ACTIVE_SHA, "source_declarations_retained_verbatim": len(names),
            "generated_declarations": ["bulksketch." + name for name in names],
            "native_source_edited": False, "native_llbc_edited": False,
            "shared_types_checked": sum(map(len, TYPE_MODULES.values())),
            "shared_types_and_function_dictionary_declarations_checked": True}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-root", type=Path)
    parser.add_argument("--dependencies", type=Path)
    args = parser.parse_args()
    print(json.dumps(check(source_root=args.source_root, dependencies=args.dependencies), indent=2))
