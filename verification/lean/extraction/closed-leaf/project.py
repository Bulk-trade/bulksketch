#!/usr/bin/env python3
"""Verify the original root-traversal declarations and their scoped imports."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/closed-leaf")
RAW = DIRECTORY / "Arithmetic"
ACTIVE = Path("bridge/Arithmetic/ClosedLeafGenerated.lean")
SOURCE = Path("src/decode/roots.rs")
SOURCE_SHA = "4697d5874fd1eb03c0210371fdac83a8dc7171de2724da046613f59c879f4fb6"
SELECTOR = "bulksketch::decode::roots::_::closed_leaf"
SPANS = {
    "charge": (70, 72),
    "stage": (99, 109),
    "advance": (110, 127),
    "closed_leaf": (237, 272),
}
OPAQUE = ["bulksketch::decode::deg34::solve", "bulksketch::decode::deg34::certificate"]
BINDINGS = {
    "decode.deg34.solve": ("bridge/Arithmetic/QuarticGenerated.lean",
                          "BulksketchBridge.QuarticSolve.solve_candidate_frames"),
    "decode.deg34.certificate": ("bridge/Arithmetic/CertificateGenerated.lean",
                                "BulksketchBridge.Certificate.certificate_refines"),
}
SCHEDULE = {
    "decode.work." + name for name in ("log2_ceil", "mul", "add", "number", "square", "square_mod",
        "number.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorDecodeError.call_once",
        "number.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorDecodeError",
        "WorkScheduleV1.cost.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorDecodeError.call_once",
        "WorkScheduleV1.cost.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorDecodeError",
        "WorkScheduleV1.cost")
}
NAMES = [
    "decode.roots.charge", "decode.roots.Roots.stage", "decode.roots.Roots.advance",
    "types.Stage.Insts.CoreCmpPartialEqStage.eq", "types.Stage.Insts.CoreCmpPartialEqStage",
    "decode.roots.Roots.closed_leaf",
]
METER = {
    "types.WorkMeter.charge.closure.Insts.CoreOpsFunctionFnOnceTupleU64Bool.call_once",
    "types.WorkMeter.charge.closure.Insts.CoreOpsFunctionFnOnceTupleU64Bool",
    "types.WorkMeter.charge",
}
SHARED_TYPES = (
    "core.ops.range.RangeToInclusive", "field.BinaryField", "backend.contract.BulkKernels",
    "backend.contract.Arithmetic", "types.RawProduct", "types.WorkMeter", "types.WorkUnits",
    "types.DecodeError", "decode.work.Charge", "decode.roots.Roots", "types.Stage",
    "decode.scratch.FactorFrame", "decode.scratch.SplitterBasis", "decode.scratch.RowWorkspace",
    "types.DecodeFailure", "types.FieldId", "field.sealed.Sealed", "types.WorkMeter.charge.closure",
    "decode.work.number.closure", "decode.work.WorkScheduleV1.cost.closure",
)
ARTIFACTS = {str(DIRECTORY / path) for path in (
    "arithmetic.llbc", "charon.log", "aeneas.log", "replay.log", "Arithmetic/Funs.lean",
    "Arithmetic/FunsExternal_Template.lean", "Arithmetic/Types.lean",
)}
HEADER = """-- Exact original-source declaration projection with existing scoped runtime bindings.
import Arithmetic.ReconstructionGenerated
import Arithmetic.QuarticGenerated
import Arithmetic.RebuiltLfsrGenerated
import Arithmetic.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxRecDepth 2048
namespace bulksketch

local notation "core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice" =>
  RebuiltLfsrRuntime.inclusive

"""


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def declarations(path):
    body = path.read_text().split("namespace bulksketch\n", 1)[1].rsplit("end bulksketch", 1)[0]
    result = {}
    for block in re.findall(r"(?ms)^/--.*?(?=^/--|\Z)", body):
        names = re.findall(r"(?m)^(?:def|impl_def|structure|inductive|abbrev)\s+(\S+)", block)
        require(len(names) == 1 and names[0] not in result, "invalid declaration block: " + str(path))
        result[names[0]] = block.strip()
    return result


def projected(root):
    definitions = declarations(root / RAW / "Funs.lean")
    require([name for name in definitions if name in NAMES] == NAMES,
            "closed-leaf declaration order or set differs")
    return HEADER + "\n\n".join(definitions[name] for name in NAMES) + "\n\nend bulksketch\n"


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    require(receipt["selector"] == SELECTOR and receipt["opaque_application_bodies"] == OPAQUE
            and receipt["native_source_edited"] is False and receipt["checked_exit"] == 0
            and receipt["source_commit"] == "0a5bda53f6b07fcae8acd870e2d0c4a246d207e6"
            and receipt["aeneas_commit"] == "ab34bd28458a08c150b7cbf1873e59af74588138"
            and receipt["charon_commit"] == "7b462d9159db2ed3015162352183906a30bfafc6"
            and receipt["binary_sha256"] == {
                "aeneas": "91f5a2776a79e2923517a2c4807c9fc017e79f185ae490502247f16e2941e330",
                "charon": "913e7969d1a0296038d115bcf1af47f8c0c6702266cc7a78a02a2b4ad7a0dfbe"}
            and receipt["aeneas_command"][1:-2] == ["-backend", "lean", "-checks", "-sequential",
                                                     "-no-progress-bar", "-print-error-emitters", "-split-files", "-dest"]
            and Path(receipt["aeneas_command"][-1]).parts[-2:] == ("closed-leaf", "arithmetic.llbc")
            and receipt["input_sha256"] == sha(root / DIRECTORY / "arithmetic.llbc"),
            "invalid checked closed-leaf receipt")
    require(set(receipt["files_sha256"]) == ARTIFACTS, "incomplete closed-leaf artifact set")
    for path, expected in receipt["files_sha256"].items():
        require(sha(root / path) == expected, "closed-leaf artifact differs: " + path)
    charon = receipt["charon_command"]
    original = receipt["aeneas_command"]
    replay = receipt["replay"]
    flags = ["-backend", "lean", "-checks", "-sequential", "-no-progress-bar",
             "-print-error-emitters", "-split-files", "-dest"]
    require(charon[1:4] == ["cargo", "--preset=aeneas", "--sysroot=default"]
            and Path(charon[0]).parts[-4:] == ("tooling", "charon", "bin", "charon")
            and charon[4].startswith("--dest-file=")
            and charon[5:9] == ["--start-from=" + SELECTOR, *("--opaque=" + name for name in OPAQUE), "--"]
            and charon[9].startswith("--manifest-path=")
            and charon[10:] == ["-p", "bulksketch", "--lib", "--locked", "--target", "x86_64-apple-darwin"],
            "closed-leaf recorded Charon command differs")
    destination = Path(charon[4].removeprefix("--dest-file="))
    require(Path(original[0]).parts[-6:] == ("tooling", "aeneas", "src", "_build", "default", "main.exe")
            and original[1:-2] == flags and Path(original[-1]) == destination
            and Path(original[-2]) == destination.parent / "stock"
            and replay["command"][:-2] == original[:-2]
            and replay["command"][-1] == original[-1]
            and Path(replay["command"][-2]).name == "closed-leaf-replay"
            and replay["exit_code"] == 0 and replay["input_sha256"] == receipt["input_sha256"]
            and replay["log_sha256"] == sha(root / DIRECTORY / "replay.log")
            and replay["outputs"] == {name: sha(root / RAW / name)
                for name in ("Types.lean", "Funs.lean", "FunsExternal_Template.lean")},
            "closed-leaf checked replay linkage differs")
    require(sha(root.parents[1] / SOURCE) == SOURCE_SHA, "frozen root traversal source differs")
    llbc = json.loads((root / DIRECTORY / "arithmetic.llbc").read_text())
    translated = llbc["translated"]
    require(llbc["has_errors"] is False and translated["options"]["start_from"] == [SELECTOR]
            and translated["options"]["opaque"] == OPAQUE, "closed-leaf LLBC closure differs")
    targets = translated["target_information"]
    require(len(targets) == 1 and targets[0]["key"] == "x86_64-apple-darwin"
            and targets[0]["value"]["target_pointer_size"] == 8, "unexpected closed-leaf target")
    found = {}
    for fn in translated["fun_decls"]:
        if not fn:
            continue
        meta = fn["item_meta"]
        name = meta["name"][-1].get("Ident", [""])[0]
        if name not in SPANS:
            continue
        span = meta["span"]["Untagged"]["data"]
        source = translated["files"][span["file_id"]]
        if source["name"] != {"Local": str(SOURCE)}:
            continue
        require(name not in found and "Structured" in fn["body"]
                and (span["beg"]["line"], span["end"]["line"]) == SPANS[name]
                and hashlib.sha256(source["contents"].encode()).hexdigest() == SOURCE_SHA,
                "closed-leaf LLBC declaration or source contents differ: " + name)
        found[name] = fn
    require(set(found) == set(SPANS), "closed-leaf LLBC declaration missing")
    types = declarations(root / RAW / "Types.lean")
    shared_types = {}
    for file in ("Types.lean", "SliceKernelTypes.lean", "ReconstructionTypes.lean",
                 "RebuiltLfsrTypes.lean", "WorkScheduleGenerated.lean", "Workmeter/Types.lean"):
        shared_types.update(declarations(root / "bridge/Arithmetic" / file)
                            if "/" not in file else declarations(root / "bridge" / file))
    require(set(types) == set(SHARED_TYPES) and all(types[name] == shared_types.get(name) for name in SHARED_TYPES),
            "closed-leaf shared type differs")
    retained = declarations(root / RAW / "Funs.lean")
    schedule = declarations(root / "bridge/Arithmetic/WorkScheduleGenerated.lean")
    require(SCHEDULE <= retained.keys() & schedule.keys()
            and all(retained[name] == schedule[name] for name in SCHEDULE), "shared work schedule declaration differs")
    meter = declarations(root / "bridge/Workmeter/Funs.lean")
    require(METER <= retained.keys() & meter.keys()
            and all(retained[name] == meter[name] for name in METER), "shared WorkMeter declaration differs")
    bindings = receipt["verified_call_bindings"]
    require(len(bindings) == len(BINDINGS)
            and {binding["generated_declaration"] for binding in bindings} == set(BINDINGS),
            "closed-leaf verified call set differs")
    for binding in bindings:
        name = binding["generated_declaration"]
        path, theorem = BINDINGS[name]
        declaration = declarations(root / path)[name]
        require(binding["generated_file"] == path and binding["theorem"] == theorem
                and hashlib.sha256(declaration.encode()).hexdigest() == binding["declaration_sha256"],
                "closed-leaf external binding differs: " + name)
    require((root / ACTIVE).read_text() == projected(root), "compiled closed-leaf projection differs")
    return {
        "raw_generated_file": str(RAW / "Funs.lean"), "raw_file_sha256": sha(root / RAW / "Funs.lean"),
        "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
        "source_declarations_retained_verbatim": len(NAMES),
        "shared_types_and_function_dictionary_declarations_checked": True,
        "generated_declarations": ["bulksketch." + name for name in NAMES],
        "native_source_edited": False,
    }


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
