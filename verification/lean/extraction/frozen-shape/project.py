#!/usr/bin/env python3
"""Bind the original stock checked frozen shape extraction to its compiled declarations."""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/frozen-shape")
ACTIVE = Path("bridge/Arithmetic/FrozenShapeGenerated.lean")
SOURCES = ("src/sketch/state.rs",)
SOURCE_COMMIT = "0a5bda53f6b07fcae8acd870e2d0c4a246d207e6"
CHARON_COMMIT = "7b462d9159db2ed3015162352183906a30bfafc6"
AENEAS_COMMIT = "ab34bd28458a08c150b7cbf1873e59af74588138"
ACTIVE_SHA = "828ec87463c23b3906b1ec790108340933918b8fa9e1dadb880351115ad09afd"
LLBC_SHA = "3b15e5bf053a5b600e1a3d337b2b2b09e3e34d26243a0b4ac42855afdd32f5cc"
RAW_SHA = "a2b25d502437c3f9f6f8136dff3acce5c46b0b5ca1a42d8c10765e07a4d0e1d3"
SELECTORS = ["bulksketch::sketch::state::_::shape"]
FLAGS = ["-backend", "lean", "-checks", "-sequential", "-no-progress-bar",
         "-print-error-emitters", "-split-files", "-dest"]
MARKER = "/-- [bulksketch::sketch::state::{bulksketch::sketch::state::FrozenSketch<F>}::shape]:"
DECLARATIONS = ["sketch.state.FrozenSketch.shape"]
FILES = {"Types.lean", "TypesExternal_Template.lean", "FunsExternal_Template.lean", "Funs.lean"}
ROW_LOCAL = Path("bridge/Arithmetic/RowLocalGenerated.lean")
TYPE_MODULES = {
    "Arithmetic/ReconstructionTypes": ("core.marker.PhantomData",),
    "Arithmetic/Types": ("types.FieldId", "field.sealed.Sealed", "field.BinaryField"),
    "Arithmetic/CandidateCompactGenerated": ("sketch.shape.SketchShape",),
    "Arithmetic/RowLocalGenerated": ("sketch.state.State", "sketch.state.FrozenSketch"),
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def type_declaration(path, name):
    match = re.search(
        r"(?m)^((?:@\[[^\n]+\]\n)*(?:def|structure|inductive) "
        + re.escape(name) + r"(?= |\n)[^\n]*(?: where| :=)[\s\S]*?)(?=\n\n)",
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
            "Invalid stock frozen shape receipt")
    for relative, expected in receipt["artifacts"].items():
        require(sha(root / relative) == expected, f"Captured frozen shape artifact differs: {relative}")
    llbc_path = directory / "arithmetic.llbc"
    require(sha(llbc_path) == LLBC_SHA, "Original frozen shape LLBC differs")
    capture = json.loads(llbc_path.read_bytes())
    crate = capture["translated"]
    options = crate["options"]
    require(capture["has_errors"] is False and options["skip_borrowck"] is False
            and options["start_from"] == options["include"] == SELECTORS
            and options["opaque"] == [], "Frozen shape capture scope differs")
    source_digests = {}
    for name in SOURCES:
        source = source_root / name
        files = [item for item in crate["files"] if item and item["name"] == {"Local": name}]
        require(len(files) == 1 and files[0]["contents"].encode() == source.read_bytes(),
                f"Frozen request source differs: {name}")
        source_digests[name] = sha(source)
    require(receipt["source_sha256"] == source_digests, "Request source receipt differs")
    ch, ae, replay = receipt["commands"]["charon"], receipt["commands"]["aeneas"], receipt["replay"]
    require(ch["exit_code"] == ae["exit_code"] == replay["exit_code"] == 0
            and ch["command"][1:4] == ["cargo", "--preset=aeneas", "--sysroot=default"]
            and ch["command"][5:7] == [*(f"--start-from={name}" for name in SELECTORS),
                                      *(f"--include={name}" for name in SELECTORS)]
            and ch["command"][-7:] == ["-p", "bulksketch", "--lib", "--locked", "--offline",
                                        "--target", "x86_64-apple-darwin"]
            and ae["command"][1:-2] == replay["command"][1:-2] == FLAGS
            and ch["command"][4].removeprefix("--dest-file=") == ae["command"][-1] == replay["command"][-1],
            "Checked frozen shape commands differ")
    generated = directory / "Arithmetic"
    output_sha = {path.name: sha(path) for path in generated.glob("*.lean")}
    require(set(output_sha) == FILES and replay["output_sha256"] == output_sha,
            "Stock frozen shape replay differs")
    for module, names in TYPE_MODULES.items():
        for name in names:
            require(type_declaration(generated / "Types.lean", name)
                    == type_declaration(dependencies / f"bridge/{module}.lean", name),
                    f"Frozen shape declaration {name} differs")
    raw_path = generated / "Funs.lean"
    active_path = root / ACTIVE
    require(sha(raw_path) == RAW_SHA and sha(active_path) == ACTIVE_SHA,
            "Compiled frozen shape projection differs")
    raw_text, active_text = raw_path.read_text(), active_path.read_text()
    require(raw_text.count(MARKER) == active_text.count(MARKER) == 1
            and active_text[active_text.index(MARKER):] == raw_text[raw_text.index(MARKER):],
            "Checked permits_id declaration differs")
    require('local notation "alloc.sync.Arc" => Id' in (dependencies / ROW_LOCAL).read_text(),
            "Existing Arc value boundary differs")
    compiled = active_text[active_text.index(MARKER):]
    names = re.findall(r"(?m)^def\s+(sketch\.[^\s]+)", compiled)
    require(names == DECLARATIONS, "Frozen shape declaration inventory differs")
    return {"raw_generated_file": str(DIRECTORY / "Arithmetic/Funs.lean"),
            "raw_file_sha256": RAW_SHA, "compiled_projection": str(ACTIVE),
            "projection_file_sha256": ACTIVE_SHA, "source_declarations_retained_verbatim": len(names),
            "shared_types_and_function_dictionary_declarations_checked": True,
            "shared_arc_value_model": str(ROW_LOCAL),
            "generated_declarations": ["bulksketch." + name for name in names],
            "native_source_edited": False, "native_llbc_edited": False,
            "shared_types_checked": sum(map(len, TYPE_MODULES.values()))}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-root", type=Path)
    parser.add_argument("--dependencies", type=Path)
    args = parser.parse_args()
    print(json.dumps(check(source_root=args.source_root, dependencies=args.dependencies), indent=2))
