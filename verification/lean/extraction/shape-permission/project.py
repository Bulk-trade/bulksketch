#!/usr/bin/env python3
"""Bind the original stock checked shape permission extraction to its compiled declarations."""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/shape-permission")
ACTIVE = Path("bridge/Arithmetic/ShapePermissionGenerated.lean")
SOURCE = Path("src/sketch/shape.rs")
SOURCE_COMMIT = "0a5bda53f6b07fcae8acd870e2d0c4a246d207e6"
CHARON_COMMIT = "7b462d9159db2ed3015162352183906a30bfafc6"
AENEAS_COMMIT = "ab34bd28458a08c150b7cbf1873e59af74588138"
ACTIVE_SHA = "b5e3195bed31973068c424bfeb580406a7504a254f52551f6b36bb4bd29bdd13"
LLBC_SHA = "706354f4fb75d9a0a8cca1accbe5abacdd79a122ec5804bc3dc06f00d2afe987"
RAW_SHA = "2f5dd760e5ce0e2a43dcb1529642ccce9e4f541f9741a970d672c0f9ff1854c1"
SHAPE = "bulksketch::sketch::shape::_::"
SELECTORS = [SHAPE + name for name in ("permits_id", "bucket_count")]
OPAQUE = [SHAPE + "bucket_for"]
FLAGS = ["-backend", "lean", "-checks", "-sequential", "-no-progress-bar",
         "-print-error-emitters", "-split-files", "-dest"]
PREFIX = "/-- [bulksketch::sketch::shape::{bulksketch::sketch::shape::SketchShape<F>}::"
MARKER = PREFIX + "permits_id]:"
COUNT = PREFIX + "bucket_count]:"
DECLARATIONS = ["sketch.shape.SketchShape.bucket_count", "sketch.shape.SketchShape.permits_id"]
FILES = {"Types.lean", "FunsExternal_Template.lean", "Funs.lean"}
REUSED = Path("bridge/Arithmetic/CandidateCompactGenerated.lean")
TYPE_MODULES = {
    "Arithmetic/ReconstructionTypes": ("core.marker.PhantomData",),
    "Arithmetic/Types": ("types.FieldId", "field.sealed.Sealed", "field.BinaryField"),
    "Arithmetic/CandidateCompactGenerated": ("sketch.shape.SketchShape",),
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
            "Invalid stock shape permission receipt")
    for relative, expected in receipt["artifacts"].items():
        require(sha(root / relative) == expected, f"Captured shape permission artifact differs: {relative}")
    llbc_path = directory / "arithmetic.llbc"
    require(sha(llbc_path) == LLBC_SHA, "Original shape permission LLBC differs")
    capture = json.loads(llbc_path.read_bytes())
    crate = capture["translated"]
    options = crate["options"]
    require(capture["has_errors"] is False and options["skip_borrowck"] is False
            and options["start_from"] == options["include"] == SELECTORS
            and options["opaque"] == OPAQUE, "Shape permission capture scope differs")
    source = source_root / SOURCE
    files = [item for item in crate["files"] if item and item["name"] == {"Local": str(SOURCE)}]
    require(len(files) == 1 and files[0]["contents"].encode() == source.read_bytes()
            and receipt["source_sha256"] == {str(SOURCE): sha(source)},
            "Frozen shape permission Rust source differs")
    ch, ae, replay = receipt["commands"]["charon"], receipt["commands"]["aeneas"], receipt["replay"]
    require(ch["exit_code"] == ae["exit_code"] == replay["exit_code"] == 0
            and ch["command"][1:4] == ["cargo", "--preset=aeneas", "--sysroot=default"]
            and ch["command"][5:10] == [*(f"--start-from={name}" for name in SELECTORS),
                                      *(f"--include={name}" for name in SELECTORS),
                                      *(f"--opaque={name}" for name in OPAQUE)]
            and ch["command"][-7:] == ["-p", "bulksketch", "--lib", "--locked", "--offline",
                                        "--target", "x86_64-apple-darwin"]
            and ae["command"][1:-2] == replay["command"][1:-2] == FLAGS
            and ch["command"][4].removeprefix("--dest-file=") == ae["command"][-1] == replay["command"][-1],
            "Checked shape permission commands differ")
    generated = directory / "Arithmetic"
    output_sha = {path.name: sha(path) for path in generated.glob("*.lean")}
    require(set(output_sha) == FILES and replay["output_sha256"] == output_sha,
            "Stock shape permission replay differs")
    for module, names in TYPE_MODULES.items():
        for name in names:
            require(type_declaration(generated / "Types.lean", name)
                    == type_declaration(dependencies / f"bridge/{module}.lean", name),
                    f"Shape permission declaration {name} differs")
    raw_path = generated / "Funs.lean"
    active_path = root / ACTIVE
    require(sha(raw_path) == RAW_SHA and sha(active_path) == ACTIVE_SHA,
            "Compiled shape permission projection differs")
    raw_text, active_text = raw_path.read_text(), active_path.read_text()
    require(raw_text.count(MARKER) == active_text.count(MARKER) == 1
            and active_text[active_text.index(MARKER):] == raw_text[raw_text.index(MARKER):],
            "Checked permits_id declaration differs")
    reused = (dependencies / REUSED).read_text()
    require(reused.count(COUNT) == raw_text.count(COUNT) == 1
            and reused[reused.index(COUNT):].split("\n\n", 1)[0]
                == raw_text[raw_text.index(COUNT):raw_text.index(MARKER)].rstrip(),
            "Reused bucket_count declaration differs")
    names = re.findall(r"(?m)^def\s+(sketch\.shape\.SketchShape\.[^\s]+)", raw_text)
    require(names == DECLARATIONS, "Shape permission declaration inventory differs")
    return {"raw_generated_file": str(DIRECTORY / "Arithmetic/Funs.lean"),
            "raw_file_sha256": RAW_SHA, "compiled_projection": str(ACTIVE),
            "projection_file_sha256": ACTIVE_SHA, "source_declarations_retained_verbatim": len(names),
            "reused_projection": str(REUSED), "reused_projection_file_sha256": sha(dependencies / REUSED),
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
