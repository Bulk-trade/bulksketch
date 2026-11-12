#!/usr/bin/env python3
"""Verify the exact original shared candidate normalization projections."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/candidate-normalize")
RAW = DIRECTORY / "Arithmetic/Funs.lean"
TYPES = DIRECTORY / "Arithmetic/Types.lean"
CAPTURE = "b4a673290d546933b1d520e4f8eecc1398ff7678ff04d74e8c76fe9c3e6aa274"
SELECTOR = "bulksketch::sketch::candidates::normalize"
NATIVE = "sketch.candidates.normalize"
SOURCE = "0a5bda53f6b07fcae8acd870e2d0c4a246d207e6"
AENEAS = "ab34bd28458a08c150b7cbf1873e59af74588138"
CHARON = "7b462d9159db2ed3015162352183906a30bfafc6"
TARGET = "x86_64-apple-darwin"
FLAGS = ["-backend", "lean", "-checks", "-sequential", "-no-progress-bar",
         "-print-error-emitters", "-split-files", "-dest"]
FILES = {"arithmetic.llbc", "charon.log", "aeneas.log", "replay.log",
         "Arithmetic/Funs.lean", "Arithmetic/Types.lean", "Arithmetic/FunsExternal_Template.lean"}
MODES = {
    "compact": ("CandidateCompactGenerated", (
        "sketch.shape.SketchShape", "sketch.shape.SketchShape.bucket_count", "sketch.shape.SketchShape.bucket_for",
        NATIVE + "_loop1.body", NATIVE + "_loop1", NATIVE + "_loop2.body", NATIVE + "_loop2",
    )),
    "merge": ("CandidateMergeGenerated", (
        NATIVE + ".closure", NATIVE + ".closure.Insts.CoreOpsFunctionFnTupleU64PairUsizeU64.call",
        NATIVE + "_loop0_loop0_loop0.body", NATIVE + "_loop0_loop0_loop0",
        NATIVE + "_loop0_loop0.body", NATIVE + "_loop0_loop0",
        NATIVE + "_loop0.body", NATIVE + "_loop0", NATIVE,
    )),
}
SHARED = {
    "Types.lean": ("field.sealed.Sealed", "types.FieldId", "field.BinaryField"),
    "ReconstructionTypes.lean": ("core.marker.PhantomData",),
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return sha256(path.read_bytes()).hexdigest()


def declarations(path):
    body = path.read_text().split("namespace bulksketch\n", 1)[1].rsplit("end bulksketch", 1)[0]
    out = {}
    for block in re.findall(r"(?ms)^/--.*?(?=^/--|\Z)", body):
        names = re.findall(r"(?m)^(?:def|structure|inductive|abbrev)\s+(\S+)", block)
        require(len(names) == 1 and names[0] not in out, "unexpected candidate normalization declaration")
        out[names[0]] = block.strip()
    return out


def check(root=ROOT, kind="merge"):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    require(receipt["selector"] == SELECTOR and receipt["source_commit"] == SOURCE
            and receipt["aeneas_commit"] == AENEAS and receipt["charon_commit"] == CHARON
            and receipt["rust_toolchain"] == "nightly-2026-09-17" and receipt["target"] == TARGET
            and receipt["native_source_edited"] is False and receipt["checked_exit"] == 0
            and receipt["binary_sha256"] == BINARIES and receipt["source_sha256"] == SOURCES,
            "candidate normalization receipt differs")
    hashes = receipt["files_sha256"]
    require(set(hashes) == {str(DIRECTORY / name) for name in FILES}, "candidate normalization artifact list differs")
    for path, expected in hashes.items():
        require(sha(root / path) == expected, "candidate normalization artifact differs: " + path)
    capture = root / DIRECTORY / "arithmetic.llbc"
    require(sha(capture) == CAPTURE and sha(root / RAW) == RAW_HASH and sha(root / TYPES) == TYPE_HASH,
            "candidate normalization frozen extraction differs")
    embedded = json.loads(capture.read_bytes())["translated"]["files"]
    for source, digest in SOURCES.items():
        contents = [x["contents"] for x in embedded if x and x["name"] == {"Local": source}]
        require(len(contents) == 1 and sha256(contents[0].encode()).hexdigest() == digest,
                "candidate normalization Rust source differs: " + source)
    ch, ae, replay = receipt["charon_command"], receipt["aeneas_command"], receipt["replay"]
    require(ch[1:4] == ["cargo", "--preset=aeneas", "--sysroot=default"]
            and ch[5:7] == ["--start-from=" + SELECTOR, "--"]
            and ch[-6:] == ["-p", "bulksketch", "--lib", "--locked", "--target", TARGET]
            and ae[1:-2] == FLAGS and ch[4].removeprefix("--dest-file=") == ae[-1]
            and replay["command"][1:-2] == FLAGS and replay["command"][-1] == ae[-1]
            and replay["exit_code"] == 0 and replay["files"] ==
              {name: sha(root / DIRECTORY / "Arithmetic" / name)
               for name in ("Funs.lean", "Types.lean", "FunsExternal_Template.lean")}
            and all("Generated:" in (root / DIRECTORY / log).read_text()
                    for log in ("aeneas.log", "replay.log")), "candidate normalization checked replay differs")
    for path, digest in RUNTIME.items():
        require(sha(root / path) == digest, "candidate normalization shared runtime differs: " + path)
    types, functions = declarations(root / TYPES), declarations(root / RAW)
    for filename, names in SHARED.items():
        shared = declarations(root / "bridge/Arithmetic" / filename)
        require(all(types[name] == shared[name] for name in names),
                "candidate normalization shared type differs: " + filename)
    original = types | functions
    module, selected = MODES[kind]
    active = Path("bridge/Arithmetic") / (module + ".lean")
    actual = declarations(root / active)
    header = (root / active).read_text().split("/-- [", 1)[0]
    require(list(actual) == list(selected) and all(actual[n] == original[n] and "sorry" not in actual[n] for n in selected)
            and sha256(header.encode()).hexdigest() == HEADERS[kind],
            "compiled candidate normalization projection differs")
    return {
        "raw_generated_file": str(RAW), "raw_file_sha256": sha(root / RAW),
        "compiled_projection": str(active), "projection_file_sha256": sha(root / active),
        "source_declarations_retained_verbatim": len(selected),
        "shared_types_and_function_dictionary_declarations_checked": True,
        "generated_declarations": ["bulksketch." + name for name in selected], "native_source_edited": False,
    }


BINARIES = {'aeneas': '91f5a2776a79e2923517a2c4807c9fc017e79f185ae490502247f16e2941e330',
 'charon': '913e7969d1a0296038d115bcf1af47f8c0c6702266cc7a78a02a2b4ad7a0dfbe'}

SOURCES = {'src/field/mod.rs': '035dc6193ebb50b324527525c0ee47cbe06ca325db16aa5f8ee55b0e79baa723',
 'src/sketch/candidates.rs': '5071c62cae68c4cc27c3d5db00697ed4412fde698f6868a6da6e266f2e1fada5',
 'src/sketch/shape.rs': 'ea2286691663eda48c422ba8bab29d69c17ca30ffaec465d0e2a5a0a4fdbc17d',
 'src/types.rs': '5702a8552c1158cf69f2155d2484f246f87475dc6bef3ea734be52348acd940d'}

RUNTIME = {'bridge/Arithmetic/DenseGcdGenerated.lean': 'f99c8048aa2b07e1397913b7971332e15fd1b6c516d78d0bb3a947d6f9c68600',
 'bridge/Arithmetic/Funs.lean': '4d688e3ce715126a0bf92d0c43cac8361de11c6f5215c01fdbf7caf8d3584ef9',
 'bridge/Arithmetic/MapsRuntime.lean': 'ebac090bd9b4f610659f8d8a34222e1c7be297e29f05e2ee335f1257f20bf02b',
 'bridge/Arithmetic/PortableEncodingRuntime.lean': '1c53f83009843ec3f7ccec47f91b257580039314bc20417bd3dfdc37057b0cd7',
 'bridge/Arithmetic/ReconstructionTypes.lean': '830fb3235ff9baf053aa13a5bf0e4844a57077a154ac51b94ec4e9e1403f5c6d',
 'bridge/Arithmetic/Types.lean': 'dd8212a82a7883d947f5788a14d7c16d0ff2a9bb95d3570910c79cc7e0b830a0'}

HEADERS = {'compact': '16e766ff519a0387715c734458931bfa8bd500522dc34f284bfac0418709eb12',
 'merge': '637915c50ede4c49ecaccac9b11f5bd89b1355697f96617e9174994f7a45a68f'}

RAW_HASH = '4a61e533b878876bf78057c02ddbd540e2f8d9b2ce356edc3a450fc4fb3c7011'

TYPE_HASH = '2518484fd1c94d8442e510b34c506e05f7164c1b6cae11be4bbf1c8f621e9f30'

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--kind", choices=MODES, default="merge")
    print(json.dumps(check(kind=parser.parse_args().kind), indent=2))
