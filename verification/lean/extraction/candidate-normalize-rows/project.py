#!/usr/bin/env python3
"""Check the exact original row-local normalization capture and projection."""
from hashlib import sha256
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/candidate-normalize-rows")
RAW = DIRECTORY / "Arithmetic/Funs.lean"
TYPES = DIRECTORY / "Arithmetic/Types.lean"
ACTIVE = Path("bridge/Arithmetic/RowLocalGenerated.lean")
VARIANT = "checked-candidate-normalize-rows-v1"
FLAG = "AENEAS_CHECKED_CANDIDATE_NORMALIZE_ROWS"
SOURCE = "0a5bda53f6b07fcae8acd870e2d0c4a246d207e6"
AENEAS = "ab34bd28458a08c150b7cbf1873e59af74588138"
CHARON = "7b462d9159db2ed3015162352183906a30bfafc6"
CAPTURE = "3ab1a8b5cac0a3efae2fb68467c3485e0cf084a6950cb2cbeacbe2aa416d29b9"
PATCH = DIRECTORY / "checked-candidate-normalize-rows.patch"
PATCH_HASH = "8b4a40d54ccb6b5ce23ab5fa8863d669a9e22a12043f9c4585f03f062c6518c4"
TARGET = "x86_64-apple-darwin"
FLAGS = ["-backend", "lean", "-checks", "-sequential", "-no-progress-bar",
         "-print-error-emitters", "-split-files", "-dest"]
OUTPUTS = {"Funs.lean", "Types.lean", "FunsExternal_Template.lean", "TypesExternal_Template.lean"}
CONTROLS = {"checked": 0, "stock": 1, "off": 1, "unchecked": 1, "wrong-name": 1,
            "wrong-span": 1, "wrong-row-type": 1, "wrong-cleanup": 1, "idle-iterator-use": 1,
            "shared-stock": 0, "shared-variant": 0, "row-stock": 0, "row-variant": 0}
ARTIFACTS = {"arithmetic.llbc", "charon.log", "checked-candidate-normalize-rows.patch", "fresh-build.log",
             "fresh-replay.log", "controls.json", "guard-controls.py",
             *("Arithmetic/" + name for name in OUTPUTS), *(name + ".log" for name in CONTROLS)}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return sha256(path.read_bytes()).hexdigest()


def declarations(path):
    body = path.read_text().split("namespace bulksketch\n", 1)[1].rsplit("end bulksketch", 1)[0]
    out = {}
    for block in re.findall(r"(?ms)^/--.*?(?=^/--|\Z)", body):
        names = re.findall(r"(?m)^(?:def|structure|inductive|abbrev|impl_def)\s+(\S+)", block)
        require(len(names) == 1 and names[0] not in out, "unexpected row-local generated declaration")
        out[names[0]] = block.strip()
    return out


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    require(receipt["variant_id"] == VARIANT and receipt["source_commit"] == SOURCE
            and receipt["aeneas_commit"] == AENEAS and receipt["charon_commit"] == CHARON
            and receipt["target"] == TARGET and receipt["rust_toolchain"] == "nightly-2026-09-17"
            and receipt["native_source_edited"] is False and receipt["native_llbc_edited"] is False
            and receipt["variant_patch"] == str(PATCH) and receipt["variant_patch_sha256"] == PATCH_HASH
            and receipt["patched_binary_sha256"] == VARIANT_BINARY
            and receipt["source_sha256"] == SOURCES, "candidate row-local receipt differs")
    files = receipt["files_sha256"]
    require(set(files) == {str(DIRECTORY / name) for name in ARTIFACTS}, "candidate row-local artifact set differs")
    for path, digest in files.items():
        require(sha(root / path) == digest, "candidate row-local artifact differs: " + path)
    capture = root / DIRECTORY / "arithmetic.llbc"
    require(sha(capture) == CAPTURE and sha(root / RAW) == RAW_HASH and sha(root / PATCH) == PATCH_HASH,
            "candidate row-local frozen capture differs")
    embedded = json.loads(capture.read_bytes())["translated"]["files"]
    for source, digest in SOURCES.items():
        contents = [x["contents"] for x in embedded if x and x["name"] == {"Local": source}]
        require(len(contents) == 1 and sha256(contents[0].encode()).hexdigest() == digest,
                "candidate row-local Rust source differs: " + source)
    build = receipt["fresh_build"]
    replay = receipt["replay"]
    outputs = {name: sha(root / DIRECTORY / "Arithmetic" / name) for name in OUTPUTS}
    require(build["status"] == 0 and build["command"][-4] == "--root"
            and build["command"][-2:] == ["-j", "2"]
            and replay["status"] == 0 and replay["command"][1:-2] == FLAGS
            and replay["flag"] == FLAG and replay["outputs"] == outputs
            and replay["command"][-1].endswith("/normalize_rows/arithmetic.llbc"),
            "candidate row-local fresh checked replay differs")
    controls = json.loads((root / DIRECTORY / "controls.json").read_text())
    require(controls["original_sha256"] == CAPTURE and controls["variant_sha256"] == VARIANT_BINARY
            and set(controls["checks"]) == set(CONTROLS), "candidate row-local controls receipt differs")
    for name, code in CONTROLS.items():
        row = controls["checks"][name]
        log = root / DIRECTORY / (name + ".log")
        flags = [f for f in FLAGS if f != "-checks" or name != "unchecked"]
        enabled = name not in ("stock", "off", "shared-stock", "row-stock")
        require(row["status"] == code and row["enabled"] is enabled and row["checked"] is (name != "unchecked")
                and row["command"][1:-2] == flags and row["log_sha256"] == sha(log),
                "candidate row-local control differs: " + name)
        if code:
            expected = ("Invariants.ml, line 914" if name in ("stock", "off", "wrong-name", "wrong-span", "wrong-row-type")
                        else "InterpReduceCollapse.ml, line 1373")
            require(expected in log.read_text(), "candidate row-local rejection differs: " + name)
    require(controls["checks"]["checked"]["outputs"] == outputs, "candidate row-local positive output differs")
    for label, folder in (("shared", "candidate-normalize"), ("row", "candidate-row")):
        stock = controls["checks"][label + "-stock"]
        variant = controls["checks"][label + "-variant"]
        path = root / "extraction" / folder
        require(stock["input_sha256"] == variant["input_sha256"] == sha(path / "arithmetic.llbc")
                and stock["outputs"] == variant["outputs"] ==
                    {name: sha(path / "Arithmetic" / name) for name in stock["outputs"]},
                "candidate row-local unrelated checked output differs: " + label)
    for path, digest in RUNTIME.items():
        require(sha(root / path) == digest, "candidate row-local shared runtime differs: " + path)
    types, functions = declarations(root / TYPES), declarations(root / RAW)
    shared = declarations(root / "bridge/Arithmetic/CandidateCompactGenerated.lean")
    require(types["sketch.shape.SketchShape"] == shared["sketch.shape.SketchShape"],
            "candidate row-local shared shape declaration differs")
    actual, original = declarations(root / ACTIVE), types | functions
    header = (root / ACTIVE).read_text().split("/-- [", 1)[0]
    require(list(actual) == SELECTED and all(actual[n] == original[n] and "sorry" not in actual[n] for n in SELECTED)
            and sha256(header.encode()).hexdigest() == HEADER, "compiled row-local candidate projection differs")
    return {
        "raw_generated_file": str(RAW), "raw_file_sha256": sha(root / RAW),
        "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
        "source_declarations_retained_verbatim": len(SELECTED),
        "shared_types_and_function_dictionary_declarations_checked": True,
        "generated_declarations": ["bulksketch." + name for name in SELECTED],
        "native_source_edited": False, "translator_variant": VARIANT,
    }


VARIANT_BINARY = '70d4ed8dedfef2b517d65621728b89075d81d43a505a8383147cac34277ade34'

SOURCES = {'src/field/mod.rs': '035dc6193ebb50b324527525c0ee47cbe06ca325db16aa5f8ee55b0e79baa723',
 'src/lib.rs': '5174f3741a1c1b0bbdfddfac894adb8d96de06896dce8960bad76fe2056fe124',
 'src/sketch/candidates.rs': '5071c62cae68c4cc27c3d5db00697ed4412fde698f6868a6da6e266f2e1fada5',
 'src/sketch/input.rs': '6c89022d5900daa757d0d5a1901c2446ec37e135610073b57cd78264c406ffaa',
 'src/sketch/mod.rs': '1f994b7873a7d5ee9b9a656c1c824cad7cdf26ef623ceb603b1f208374842f58',
 'src/sketch/shape.rs': 'ea2286691663eda48c422ba8bab29d69c17ca30ffaec465d0e2a5a0a4fdbc17d',
 'src/sketch/state.rs': '516876d63076bf34f5b37bcf47a8ca557cc22b1b1615124522b6853f9b8b3b45',
 'src/types.rs': '5702a8552c1158cf69f2155d2484f246f87475dc6bef3ea734be52348acd940d'}

RUNTIME = {'bridge/Arithmetic/CandidateCompactGenerated.lean': 'd259a42979c247fb9f5691e7a9e9401d8cd9f2e2dfdff54742386ec557353d75',
 'bridge/Arithmetic/DegreeProbeRuntime.lean': 'b4660ff42f0a56adfcbd4a9cdeae191e27c17f56d61feeea1a5f2010158bc271',
 'bridge/Arithmetic/Funs.lean': '4d688e3ce715126a0bf92d0c43cac8361de11c6f5215c01fdbf7caf8d3584ef9',
 'bridge/Arithmetic/ReconstructionTypes.lean': '830fb3235ff9baf053aa13a5bf0e4844a57077a154ac51b94ec4e9e1403f5c6d'}

RAW_HASH = '32cfbe7fad891270458cd519695697472c4f6038ce8d20fbcdbc806938c8a3cf'

HEADER = 'eaa78b36a90fb1a645976657a54a4088e55829bee0194d69d4237269d8fb191a'

SELECTED = ['sketch.state.State',
 'sketch.state.FrozenSketch',
 'sketch.input.DecodeRow',
 'sketch.candidates.normalize_rows.closure',
 'sketch.candidates.normalize_rows.closure.Insts.CoreOpsFunctionFnMutTupleShared0DecodeRowUsize.call_mut',
 'sketch.candidates.normalize_rows.closure.Insts.CoreOpsFunctionFnOnceTupleShared0DecodeRowUsize.call_once',
 'sketch.candidates.normalize_rows.closure.Insts.CoreOpsFunctionFnOnceTupleShared0DecodeRowUsize',
 'sketch.candidates.normalize_rows.closure.Insts.CoreOpsFunctionFnMutTupleShared0DecodeRowUsize',
 'sketch.candidates.normalize_rows_loop0_loop0.body',
 'sketch.candidates.normalize_rows_loop0_loop0',
 'sketch.candidates.normalize_rows_loop0.body',
 'sketch.candidates.normalize_rows_loop0',
 'sketch.candidates.normalize_rows']

if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
