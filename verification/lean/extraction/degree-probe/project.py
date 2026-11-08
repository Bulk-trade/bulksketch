#!/usr/bin/env python3
"""Check the original DegreeProbe projection and scoped Rust std bindings."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/degree-probe")
RAW = DIRECTORY / "Arithmetic"
ACTIVE = Path("bridge/Arithmetic/DegreeProbeGenerated.lean")
RUNTIME = Path("bridge/Arithmetic/DegreeProbeRuntime.lean")
SOURCE = Path("src/decode/degree_probe.rs")
SELECTOR = "bulksketch::decode::degree_probe"
VARIANT = "checked-fixedpoint-nested-scalar-slice-retry-v1"
SOURCE_COMMIT = "0a5bda53f6b07fcae8acd870e2d0c4a246d207e6"
SOURCE_SHA = "60d72b0aa11f311c4359bfe94f0d6fede00723602b3251492cbdb10ee51752ed"
GUARD = Path("extraction/deg34-guard")
WORKSPACE_TYPES = ("decode.degree_probe.DegreeProbe", "types.Stage", "decode.row.RowBudget", "decode.scratch.RowWorkspace")
CLOSURES = ("decode.probe.verified.closure_1", "decode.probe.verified.closure")
METHODS = ["decode.degree_probe.DegreeProbe." + method for method in ("new", "next_stage", "impl.count", "reject")]
RUN = "decode.degree_probe.DegreeProbe.run"
ARTIFACTS = {str(DIRECTORY / path) for path in (
    "arithmetic.llbc", "charon.log", "aeneas.log", "pinned.log", "unchecked.log",
    "Arithmetic/Funs.lean", "Arithmetic/Types.lean", "Arithmetic/FunsExternal_Template.lean",
    "controls/baseline.log", "controls/native-sort.log", "controls/unsigned-sort-control.rs")}
DEPENDENCIES = {
    "Arithmetic/NewtonGuardGenerated.lean": ("decode.deg34.guard",),
    "Arithmetic/NormalizeGenerated.lean": ("decode.deg34.normalize",),
    "Arithmetic/QuarticGenerated.lean": ("decode.deg34.quartic", "decode.deg34.solve"),
    "Arithmetic/CertificateGenerated.lean": ("decode.deg34.certificate",),
    "Arithmetic/AffineQuarticGenerated.lean": ("decode.deg34.affine_quartic",),
    "Arithmetic/WorkScheduleGenerated.lean": ("decode.work.WorkScheduleV1.cost", "decode.work.number", "decode.work.Charge"),
    "Workmeter/Funs.lean": ("types.WorkMeter.charge",),
}
HEADER = """-- Exact original DegreeProbe declarations with scoped standard-library bindings.
import Arithmetic.ReconstructionTypes
import Arithmetic.WorkScheduleGenerated
import Arithmetic.QuarticGenerated
import Arithmetic.RebuiltLfsrGenerated
import Arithmetic.Funs
import Arithmetic.NewtonGuardGenerated
import Arithmetic.NormalizeGenerated
import Arithmetic.DegreeProbeRuntime

namespace bulksketch

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false
set_option maxRecDepth 2048
set_option maxHeartbeats 1500000

local notation "core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice" =>
  RebuiltLfsrRuntime.inclusive
local notation "Mut1A.Insts.CoreCmpPartialEqShared0B.eq" => CertificateRuntime.mutableSharedEq
local notation "core.bool.Bool.then_some" => CubeRootRuntime.thenSome
local notation "U8.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from" =>
  Aeneas.Std.DegreeProbeRuntime.usizeToU8
local notation "core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.fold" =>
  Aeneas.Std.DegreeProbeRuntime.foldShared
local notation "core.slice.Slice.sort_unstable" =>
  (fun (_ : core.cmp.Ord U64) => Aeneas.Std.DegreeProbeRuntime.sortUnsigned)

"""


def require(valid, message):
    if not valid:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def blocks(path):
    body = path.read_text().split("namespace bulksketch\n", 1)[1].rsplit("end bulksketch", 1)[0]
    found = {}
    for block in re.findall(r"(?ms)^/--.*?(?=^/--|\Z)", body):
        match = re.findall(r"(?m)^(?:def|impl_def|structure|inductive|abbrev)\s+(\S+)", block)
        require(len(match) == 1 and match[0] not in found, "invalid DegreeProbe declaration block: " + str(path))
        found[match[0]] = block.strip()
    return found


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    require(receipt["status"] == "checked_original_closure_extracted" and receipt["selected_root"] == SELECTOR
            and receipt["source_commit"] == SOURCE_COMMIT and receipt["source_sha256"] == SOURCE_SHA
            and receipt["candidate_variant"] == VARIANT and receipt["native_source_edited"] is False
            and receipt["transparent_application_bodies"] is True and receipt["llbc_has_errors"] is False,
            "invalid DegreeProbe extraction receipt")
    require(set(receipt["files_sha256"]) == ARTIFACTS, "incomplete DegreeProbe artifact set")
    for path, digest in receipt["files_sha256"].items():
        require(sha(root / path) == digest, "DegreeProbe artifact differs: " + path)
    require(sha(root / RUNTIME) == receipt["scoped_runtime_sha256"], "DegreeProbe scoped runtime differs")
    require(sha(root.parents[1] / SOURCE) == SOURCE_SHA, "frozen DegreeProbe Rust source differs")
    translator = json.loads((root / GUARD / "receipt.json").read_text())
    require(receipt["guard_projection_receipt_sha256"] == sha(root / GUARD / "receipt.json")
            and receipt["full_patch_sha256"] == translator["full_patch_sha256"]
            == sha(root / GUARD / "translator/checked-nested-slice-loan-retry.patch")
            and translator["candidate_variant"] == VARIANT, "DegreeProbe translator provenance differs")
    commands = {entry["name"]: entry for entry in receipt["checks"]}
    require(len(commands) == len(receipt["checks"]) and
            {key: entry["exit_code"] for key, entry in commands.items()} ==
            {"charon": 0, "Arithmetic": 0, "replay": 0, "pinned": 1, "unchecked": 1}
            and receipt["replayed_files_byte_identical"] == 3, "DegreeProbe translator command matrix differs")
    llbc_sha = sha(root / DIRECTORY / "arithmetic.llbc")
    for name, log in (("replay", "aeneas.log"), ("pinned", "pinned.log"), ("unchecked", "unchecked.log")):
        command = commands[name]
        flags = set(command["command"])
        require(sha(root / DIRECTORY / log) == command["log_sha256"] and command["input_sha256"] == llbc_sha
                and "-sequential" in flags and ("-checks" in flags) == (name != "unchecked"),
                "DegreeProbe translator log, input, or flags differ")
        if name != "replay":
            require("src/decode/deg34.rs', lines 49:8-57:9" in (root / DIRECTORY / log).read_text(),
                    "DegreeProbe negative extraction does not reject the original guard")
    llbc = json.loads((root / DIRECTORY / "arithmetic.llbc").read_text())
    translated = llbc["translated"]
    require(llbc["has_errors"] is False and translated["options"]["start_from"] == [SELECTOR]
            and translated["options"]["opaque"] == [], "DegreeProbe LLBC closure differs")
    target = translated["target_information"]
    require(len(target) == 1 and target[0]["key"] == "x86_64-apple-darwin"
            and target[0]["value"]["target_pointer_size"] == 8, "unexpected DegreeProbe target")
    prefix = [{"Ident": [part, 0]} for part in SELECTOR.split("::")]
    run = [fn for fn in translated["fun_decls"] if fn and fn["item_meta"]["name"][:3] == prefix
           and fn["item_meta"]["name"][-1] == {"Ident": ["run", 0]}]
    require(len(run) == 1 and "Structured" in run[0]["body"], "original DegreeProbe::run body missing")
    span = run[0]["item_meta"]["span"]["Untagged"]["data"]
    source = translated["files"][span["file_id"]]
    require(span["beg"] == {"line": 51, "col": 4} and span["end"] == {"line": 139, "col": 5}
            and source["name"] == {"Local": str(SOURCE)}
            and hashlib.sha256(source["contents"].encode()).hexdigest() == SOURCE_SHA,
            "DegreeProbe LLBC source span or contents differ")
    types, functions = (blocks(root / RAW / (file + ".lean")) for file in ("Types", "Funs"))
    both = types | functions
    reused_count = 0
    for file, prefixes in DEPENDENCIES.items():
        reused = {name: block for name, block in blocks(root / "bridge" / file).items() if name.startswith(prefixes)}
        require(reused and all(both.get(name) == block for name, block in reused.items()),
                "shared DegreeProbe declarations differ: " + file)
        reused_count += len(reused)
    workspace = blocks(root / "bridge/Arithmetic/ReconstructionTypes.lean")
    require(all(types[name] == workspace[name] for name in WORKSPACE_TYPES), "shared DegreeProbe workspace types differ")
    equality = "Slice.Insts.CoreCmpPartialEqSlice"
    reused_equality = blocks(root / "bridge/Arithmetic/RebuiltLfsrGenerated.lean")[equality]
    require(reused_equality.split("\n  ne :=", 1)[0].replace("\nimpl_def ", "\ndef ") + "\n}" == functions[equality],
            "shared DegreeProbe slice equality differs")
    verified = [name for name in functions if name.startswith("decode.probe.verified")]
    selected = [*METHODS, *verified, RUN]
    require(len(verified) == 9 and sum(functions[name].count("core.slice.Slice.sort_unstable") for name in selected) == 1
            and "core.slice.Slice.sort_unstable core.cmp.OrdU64 s" in functions[RUN],
            "DegreeProbe unsigned sort binding is outside its source scope")
    projection = HEADER + "\n\n".join(both[name] for name in (*CLOSURES, *selected)) + "\n\nend bulksketch\n"
    require((root / ACTIVE).read_text() == projection, "compiled DegreeProbe projection differs")
    return {
        "raw_generated_file": str(RAW / "Funs.lean"), "raw_file_sha256": sha(root / RAW / "Funs.lean"),
        "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
        "source_declarations_retained_verbatim": len(selected), "source_type_declarations_retained_verbatim": len(CLOSURES),
        "shared_types_and_function_dictionary_declarations_checked": True, "shared_declarations_checked": reused_count + 5,
        "generated_declarations": ["bulksketch." + name for name in selected],
        "translator_variant": VARIANT, "native_source_edited": False,
    }


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
