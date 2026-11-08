#!/usr/bin/env python3
"""Check the source-pinned reconstruction wrapper and both original loops."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
EXTRACTION = Path("extraction/reconstruction")
RAW = EXTRACTION / "Arithmetic"
ACTIVE = Path("bridge/Arithmetic/ReconstructionGenerated.lean")
TYPES = Path("bridge/Arithmetic/ReconstructionTypes.lean")
VARIANT = "checked-ended-projector-leaf-v1"
MATCHER = Path("tooling/aeneas-ended-projector")
SOURCE = Path("src/decode/stages.rs")
SOURCE_SHA = "93825fcb5054e98e9af060a81da72d4770c29354d79822ccfc949cc55f6e9b23"
SOURCE_COMMIT = "0a5bda53f6b07fcae8acd870e2d0c4a246d207e6"
BASE = "decode.stages.Execution.reconstruct"
FN_MUT = BASE + ".closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool"
FN_ONCE = BASE + ".closure.Insts.CoreOpsFunctionFnOnceTupleShared0U64Bool"
FUNCTIONS = [FN_MUT + ".call_mut", FN_ONCE + ".call_once", FN_ONCE, FN_MUT,
             BASE + "_loop0.body", BASE + "_loop0", BASE + "_loop1.body", BASE + "_loop1", BASE]
TYPE_NAMES = [
    "core.marker.PhantomData", "types.Stage", "decode.degree_probe.DegreeProbe", "decode.roots.Roots",
    "types.DecodeFailure", "decode.row.RowBudget", "decode.row.RowInput", "decode.scratch.FactorFrame",
    "decode.scratch.SplitterBasis", "decode.scratch.RowWorkspace", "decode.stages.State",
    "decode.stages.Execution", BASE + ".closure",
]
SHARED_TYPES = {
    "bridge/Arithmetic/Types.lean": ("types.RawProduct", "types.FieldId", "field.sealed.Sealed", "field.BinaryField"),
    "bridge/Arithmetic/SliceKernelTypes.lean": ("backend.contract.Arithmetic", "backend.contract.BulkKernels"),
    "bridge/Workmeter/Types.lean": ("types.WorkUnits", "types.WorkMeter", "types.DecodeError"),
    "bridge/Arithmetic/WorkScheduleGenerated.lean": ("decode.work.Charge",),
}
ARTIFACTS = {
    "arithmetic.llbc", "charon.log", "aeneas.log", "pinned.log", "unchecked.log",
    "Arithmetic/Types.lean", "Arithmetic/Funs.lean", "Arithmetic/FunsExternal_Template.lean",
}
HEADER = "-- Exact declarations projected from the original reconstruction extraction.\n"
PRELUDE = """open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
namespace bulksketch

"""
TYPE_HEADER = HEADER + """module
public import Arithmetic.SliceKernelTypes
public import Workmeter.Types
@[expose] public section
""" + PRELUDE
FUN_HEADER = HEADER + """import Arithmetic.ReconstructionRuntime
import Arithmetic.ReconstructionWorkspace
import Arithmetic.WorkScheduleGenerated
""" + PRELUDE + """local notation "core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all" => Aeneas.Std.ReconstructionRuntime.sliceAll
local notation "decode.stages.check_workspace" => BulksketchBridge.Reconstruction.checkWorkspace

"""


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def declarations(path):
    body = path.read_text().split("namespace bulksketch\n", 1)[1].rsplit("end bulksketch", 1)[0]
    items = {}
    for block in re.findall(r"(?ms)^/--.*?(?=^/--|\Z)", body):
        names = re.findall(r"(?m)^(?:def|impl_def|structure|inductive|abbrev)\s+(\S+)", block)
        require(len(names) == 1 and names[0] not in items, "unexpected declaration: " + str(path))
        items[names[0]] = block.strip()
    return items


def check(root=ROOT):
    receipt = json.loads((root / EXTRACTION / "receipt.json").read_text())
    matcher = json.loads((root / MATCHER / "receipt.json").read_text())
    require(receipt["status"] == "checked_original_body_extracted" and
            receipt["source_commit"] == SOURCE_COMMIT and receipt["native_source_edited"] is False and
            receipt["translator_variant"] == matcher["variant_id"] == VARIANT and
            receipt["aeneas_commit"] == matcher["base_aeneas_commit"] and
            receipt["charon_commit"] == matcher["charon_commit"] and
            receipt["patch_sha256"] == matcher["patch_sha256"] ==
                sha(root / MATCHER / "ended-projector-leaf.patch") and
            receipt["llbc_has_errors"] is False and receipt["source_sha256"] == SOURCE_SHA and
            receipt["same_reconstruct_declarations_as_unfiltered_checked_attempt"] is True,
            "reconstruction lost checked translator provenance")
    artifacts = receipt["artifacts"]
    require(set(artifacts) == ARTIFACTS, "reconstruction artifact set changed")
    for name, digest in artifacts.items():
        path = EXTRACTION / name
        require(sha(root / path) == digest, "raw reconstruction artifact differs: " + str(path))
    commands = {item["name"]: item for item in receipt["commands"]}
    require(len(commands) == len(receipt["commands"]) and
            {name: entry["exit_code"] for name, entry in commands.items()} ==
                {"charon": 0, "Arithmetic": 0, "pinned": 1, "unchecked": 1} and
            all({"-checks", "-sequential"} <= set(commands[name]["command"])
                for name in ("Arithmetic", "pinned")) and
            "-checks" not in commands["unchecked"]["command"] and
            "-sequential" in commands["unchecked"]["command"] and
            all(Path(commands[name]["command"][-1]).name == "arithmetic.llbc"
                for name in ("Arithmetic", "pinned", "unchecked")),
            "reconstruction checked and unchecked controls changed")
    require(sha(root.parents[1] / SOURCE) == SOURCE_SHA, "frozen reconstruction Rust source differs")
    llbc = json.loads((root / EXTRACTION / "arithmetic.llbc").read_text())
    translated = llbc["translated"]
    prefix = "bulksketch::decode::stages"
    require(llbc["has_errors"] is False and translated["options"]["start_from"] == [prefix] and
            translated["options"]["opaque"] == [prefix + "::_::_", prefix + "::check_workspace"] and
            translated["options"]["include"] == [prefix + "::_::reconstruct", prefix + "::_::charge"],
            "original reconstruction extraction selection changed")
    targets = translated["target_information"]
    require(len(targets) == 1 and targets[0]["key"] == "x86_64-apple-darwin" and
            targets[0]["value"]["target_pointer_size"] == 8, "unexpected reconstruction target")
    roots = {}
    for fn in translated["fun_decls"]:
        if not fn:
            continue
        name = fn["item_meta"]["name"]
        span = fn["item_meta"]["span"]
        if "Untagged" not in span:
            continue
        span = span["Untagged"]["data"]
        file = translated["files"][span["file_id"]]
        if file["name"] == {"Local": str(SOURCE)} and name[-1].get("Ident", [None])[0] in (
                "reconstruct", "charge", "check_workspace"):
            roots[name[-1]["Ident"][0]] = fn["body"], span["beg"], span["end"], file["contents"]
    for name, start, end, col in (("charge", 163, 165, 4), ("reconstruct", 241, 265, 4),
                                  ("check_workspace", 454, 487, 0)):
        body, begin, stop, content = roots[name]
        require(begin == {"line": start, "col": col} and stop == {"line": end, "col": col + 1} and
                hashlib.sha256(content.encode()).hexdigest() == SOURCE_SHA and
                (body == "Opaque" if name == "check_workspace" else "Structured" in body),
                "original reconstruction root span or opacity changed: " + name)
    types = declarations(root / RAW / "Types.lean")
    functions = declarations(root / RAW / "Funs.lean")
    for path, names in SHARED_TYPES.items():
        shared = declarations(root / path)
        require(all(types[name] == shared[name] for name in names), "shared reconstruction type differs: " + path)
    work = declarations(root / "bridge/Arithmetic/WorkScheduleGenerated.lean")
    meter = declarations(root / "bridge/Workmeter/Funs.lean")
    for name, shared in (("decode.stages.Execution.charge", work), ("types.WorkMeter.charge", meter)):
        require(functions[name] == shared[name], "shared reconstruction callback differs: " + name)
    require([name for name in functions if name.startswith(BASE)] == FUNCTIONS and
            {name: hashlib.sha256(functions[name].encode()).hexdigest() for name in FUNCTIONS} ==
                receipt["reconstruct_declarations_sha256"], "reconstruction emitted body changed")
    type_output = TYPE_HEADER + "".join(types[name] + "\n\n" for name in TYPE_NAMES) + "end bulksketch\n"
    require((root / TYPES).read_text() == type_output, "compiled reconstruction types differ")
    output = FUN_HEADER + "".join(functions[name] + "\n\n" for name in FUNCTIONS) + "end bulksketch\n"
    require((root / ACTIVE).read_text() == output, "compiled reconstruction projection differs")
    return {
        "raw_generated_file": str(RAW / "Funs.lean"), "raw_file_sha256": sha(root / RAW / "Funs.lean"),
        "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
        "source_declarations_retained_verbatim": len(FUNCTIONS),
        "source_type_declarations_retained_verbatim": len(TYPE_NAMES),
        "shared_types_and_function_dictionary_declarations_checked": True,
        "generated_declarations": ["bulksketch." + name for name in FUNCTIONS],
        "translator_variant": VARIANT, "native_source_edited": False,
    }


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
