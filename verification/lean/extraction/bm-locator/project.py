#!/usr/bin/env python3
"""Check the exact original BM locator extraction and zero-credit Lean projection."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
EXTRACTION = "extraction/bm-locator"
COMPILED = "bridge/Arithmetic/BmLocatorGenerated.lean"
RUNTIME = "bridge/Arithmetic/BmLocatorRuntime.lean"
SOURCE = "src/decode/bm.rs"
NATIVE_ID = "src/decode/bm.rs:13:function:bulksketch::decode::bm::locator"
SOURCE_COMMIT = "0a5bda53f6b07fcae8acd870e2d0c4a246d207e6"
LLBC_SHA = "fe142482151f5de52ee35b51279587bef08887ae6f70f118f099f83be72a523c"
VARIANT = "checked-bm-locator-v1"
BASE = "ab34bd28458a08c150b7cbf1873e59af74588138"
CHARON = "7b462d9159db2ed3015162352183906a30bfafc6"
PATCH = EXTRACTION + "/checked-bm-locator.patch"
TARGET = "aarch64-apple-darwin"
SOURCES = {"src/Config.ml", "src/PrePasses.ml", "src/interp/InterpMatchCtxs.ml",
           "src/interp/InterpStatements.ml", "src/symbolic/SymbolicToPureExpressions.ml"}
ENVIRONMENT = {"BULKSKETCH_BM_LOCATOR": "1"}
POSITIVE_COUNTS = {
    "BM-DYNAMIC-SHARED-PRE": 10,
    "BM-DYNAMIC-LATER-POST restored=true all_other_bindings_preserved=true": 20,
    "BM-EXACT-DENSE-ERASE": 2,
    "BM-ZIP-MIRROR-MATCH": 4,
    "BM-ZIP-MIRROR-WRITEBACK": 8,
}
ARTIFACTS = {f"{EXTRACTION}/{name}" for name in (
    "arithmetic.llbc", "charon.log", "checked.log", "replay.log", "disabled.log",
    "unchecked.log", "portable-xor.log", "portable-xor-baseline.log",
    "Arithmetic/Types.lean", "Arithmetic/Funs.lean", "Arithmetic/FunsExternal_Template.lean",
)}
GENERATED = {f"{EXTRACTION}/Arithmetic/{name}" for name in (
    "Types.lean", "Funs.lean", "FunsExternal_Template.lean",
)}
FUNCTIONS = [f"decode.bm.locator_loop0_loop{index}{suffix}" for index in range(11)
             for suffix in (".body", "")] + [
    "decode.bm.locator_loop0.body", "decode.bm.locator_loop0", "decode.bm.locator",
]
TYPES = {
    "core.ops.range.RangeToInclusive": "bridge/Arithmetic/RebuiltLfsrTypes.lean",
    **dict.fromkeys(("types.RawProduct", "types.FieldId", "field.sealed.Sealed", "field.BinaryField"),
                    "bridge/Arithmetic/Types.lean"),
    **dict.fromkeys(("backend.contract.Arithmetic", "backend.contract.BulkKernels"),
                    "bridge/Arithmetic/SliceKernelTypes.lean"),
    **dict.fromkeys(("types.WorkMeter.charge.closure", "types.WorkUnits", "types.WorkMeter",
                     "types.DecodeError"), "bridge/Workmeter/Types.lean"),
    "types.DecodeFailure": "bridge/Arithmetic/ReconstructionTypes.lean",
    **dict.fromkeys(("decode.work.number.closure", "decode.work.WorkScheduleV1.cost.closure",
                     "decode.work.Charge"), "bridge/Arithmetic/WorkScheduleGenerated.lean"),
}
SHARED_FUNCTIONS = {
    **dict.fromkeys(("types.WorkMeter.charge.closure.Insts.CoreOpsFunctionFnOnceTupleU64Bool.call_once",
                     "types.WorkMeter.charge.closure.Insts.CoreOpsFunctionFnOnceTupleU64Bool",
                     "types.WorkMeter.charge"), "bridge/Workmeter/Funs.lean"),
    **dict.fromkeys(("decode.work.log2_ceil", "decode.work.mul", "decode.work.add",
                     "decode.work.number.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorDecodeError.call_once",
                     "decode.work.number.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorDecodeError",
                     "decode.work.number", "decode.work.square", "decode.work.square_mod",
                     "decode.work.WorkScheduleV1.cost.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorDecodeError.call_once",
                     "decode.work.WorkScheduleV1.cost.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorDecodeError",
                     "decode.work.WorkScheduleV1.cost"), "bridge/Arithmetic/WorkScheduleGenerated.lean"),
    "core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT":
        "bridge/Arithmetic/DenseNormalizationGenerated.lean",
}
RUNTIMES = {RUNTIME, "bridge/Arithmetic/MutableZipRuntime.lean",
            "bridge/Arithmetic/RebuiltLfsrRuntime.lean", "bridge/Arithmetic/PortableEncodingRuntime.lean",
            "bridge/Workmeter/FunsExternal.lean", "bridge/Arithmetic/WorkScheduleRuntime.lean"}
HEADER = """-- Exact original locator declaration projection with scoped standard-library bindings.
import Arithmetic.WorkScheduleGenerated
import Arithmetic.ReconstructionTypes
import Arithmetic.RebuiltLfsrRuntime
import Arithmetic.PortableEncodingRuntime
import Arithmetic.DenseNormalizationGenerated
import Arithmetic.MutableZipRuntime
import Arithmetic.BmLocatorRuntime

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

noncomputable section
namespace bulksketch

local notation "core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice" =>
  Aeneas.Std.RebuiltLfsrRuntime.inclusive
local notation "core.ops.range.RangeInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice" =>
  Aeneas.Std.BmLocatorRuntime.inclusiveRange
local notation "core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator" =>
  Aeneas.Std.BmLocatorRuntime.reverseIterator
/- The two original dictionary heads select existing shared and mutable
operations with their distinct Result shapes. This affects only this projection. -/
local macro "core.iter.traits.iterator.Iterator.zip.trait_default"
    leftDict:term:arg rightDict:term:arg left:term:arg input:term:arg : term =>
  match leftDict with
  | `((core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT $_)) =>
      `(Aeneas.Std.MutableZip.construct $rightDict $left $input)
  | `((core.iter.traits.iterator.IteratorSliceIter $_)) =>
      `(Aeneas.Std.core.iter.traits.iterator.Iterator.zip.trait_default
        $leftDict $rightDict $left $input)
  | _ => Lean.Macro.throwErrorAt leftDict "Unrecognized original BM Zip constructor dictionary"

local macro "core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next"
    leftDict:term:arg rightDict:term:arg state:term:arg : term =>
  match leftDict with
  | `((core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT $_)) =>
      `(Aeneas.Std.MutableZip.next $leftDict $rightDict $state)
  | `((core.iter.traits.iterator.IteratorSliceIter $_)) =>
      `(Aeneas.Std.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
        $leftDict $rightDict $state)
  | _ => Lean.Macro.throwErrorAt leftDict "Unrecognized original BM Zip step dictionary"

"""


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(valid, message):
    if not valid:
        raise ValueError(message)


def blocks(path):
    body = path.read_text().split("namespace bulksketch\n", 1)[1].rsplit("end bulksketch", 1)[0]
    result = {}
    for block in re.findall(r"(?ms)^/--.*?(?=^/--|\Z)", body):
        names = re.findall(r"(?m)^(?:def|impl_def|structure|inductive|abbrev)\s+(\S+)", block)
        if names:
            require(len(names) == 1 and names[0] not in result, "ambiguous declaration in " + str(path))
            result[names[0]] = block
    return result


def project(root):
    raw = root / EXTRACTION / "Arithmetic/Funs.lean"
    funs = blocks(raw)
    types = blocks(root / EXTRACTION / "Arithmetic/Types.lean")
    retained = [name for name in funs if name.startswith("decode.bm.locator")]
    require(retained == FUNCTIONS, "original BM locator declaration set changed")
    require(list(types) == list(TYPES), "original BM locator type set changed")
    files = set(TYPES.values()) | set(SHARED_FUNCTIONS.values())
    shared = {file: blocks(root / file) for file in files}
    for names, declarations in ((TYPES, types), (SHARED_FUNCTIONS, funs)):
        for name, file in names.items():
            require(declarations[name].rstrip() == shared[file][name].rstrip(),
                    "shared BM declaration differs: " + name)
    projected = HEADER + "".join(funs[name] for name in retained) + "end bulksketch\n"
    require((root / COMPILED).read_text() == projected, "compiled BM locator projection differs")
    return raw, retained


def check(root=ROOT):
    receipt = json.loads((root / EXTRACTION / "receipt.json").read_text())
    require(receipt["status"] == "generated" and receipt["source_commit"] == SOURCE_COMMIT
            and receipt["aeneas_commit"] == BASE and receipt["charon_commit"] == CHARON
            and receipt["variant_id"] == VARIANT and receipt["target"] == TARGET
            and receipt["native_body_proof_credit"] == 0 and receipt["native_source_edited"] is False
            and receipt["source_selector"] == "bulksketch::decode::bm::locator",
            "BM locator receipt lacks the exact source and tool pins")
    require(len(receipt["artifacts"]) == len(ARTIFACTS)
            and {entry["path"] for entry in receipt["artifacts"]} == ARTIFACTS,
            "BM raw artifact set changed")
    for item in receipt["artifacts"]:
        require(sha(root / item["path"]) == item["sha256"], "BM raw artifact differs: " + item["path"])
    patch = (root / PATCH).read_text()
    changed = re.findall(r"(?m)^diff --git a/(\S+) b/(\S+)$", patch)
    require(receipt["variant_patch"] == PATCH and sha(root / PATCH) == receipt["variant_patch_sha256"]
            and len(changed) == len(SOURCES) and set(changed) == {(path, path) for path in SOURCES}
            and set(receipt["modified_sources"]) == set(receipt["base_sources"]) == SOURCES,
            "BM translator patch or source scope differs")
    require(set(receipt["runtime_files_sha256"]) == RUNTIMES,
            "BM runtime dependency set differs")
    for file, expected in receipt["runtime_files_sha256"].items():
        require(sha(root / file) == expected, "BM runtime binding differs: " + file)
    raw_llbc = root / EXTRACTION / "arithmetic.llbc"
    require(sha(raw_llbc) == LLBC_SHA == receipt["llbc_sha256"], "original BM LLBC differs")
    llbc = json.loads(raw_llbc.read_text())
    translated = llbc["translated"]
    require(llbc["has_errors"] is False and receipt["llbc_has_errors"] is False
            and translated["crate_name"] == "bulksketch"
            and [item["key"] for item in translated["target_information"]] == [TARGET]
            and translated["options"]["start_from"] == ["bulksketch::decode::bm::locator"],
            "BM LLBC target or selector differs")
    source = (root.parent.parent / SOURCE).read_text()
    require(translated["files"][6]["name"] == {"Local": SOURCE}
            and translated["files"][6]["contents"] == source, "BM LLBC native source text differs")
    item = translated["fun_decls"][11]["item_meta"]
    span = item["span"]["Untagged"]["data"]
    require(item["name"] == [{"Ident": [name, 0]} for name in ("bulksketch", "decode", "bm", "locator")]
            and span == {"file_id": 6, "beg": {"line": 14, "col": 0}, "end": {"line": 98, "col": 1}}
            and item["source_text"] == "".join(source.splitlines(keepends=True)[13:97]) + "}",
            "BM LLBC original locator association differs")
    extraction = receipt["checked_extraction"]
    require(extraction["input"] == str(raw_llbc.relative_to(root))
            and extraction["input_sha256"] == LLBC_SHA and extraction["exit_code"] == 0
            and set(extraction["required_flags"]) == {"-checks", "-sequential"}
            and set(extraction["required_flags"]) <= set(extraction["command"])
            and extraction["environment"] == ENVIRONMENT
            and len(extraction["generated"]) == len(GENERATED)
            and {item["path"] for item in extraction["generated"]} == GENERATED
            and all(sha(root / item["path"]) == item["sha256"] for item in extraction["generated"]),
            "checked BM extraction provenance differs")
    replay = receipt["replay"]
    require(replay["exit_code"] == 0 and {"-checks", "-sequential"} <= set(replay["command"])
            and replay["environment"] == ENVIRONMENT
            and replay["exact_generated_artifacts"] == len(GENERATED)
            and receipt["checked_event_counts"] == POSITIVE_COUNTS, "BM checked replay differs")
    for record in (extraction, replay):
        log_path = root / EXTRACTION / (record["name"] + ".log")
        log = log_path.read_text()
        require(sha(log_path) == record["log_sha256"] and "Generated the partial file" not in log
                and all(log.count(marker) == count for marker, count in POSITIVE_COUNTS.items()),
                "BM checked writeback evidence differs")
    controls = receipt["controls"]
    require(set(controls) == {"disabled", "unchecked", "portable-xor", "portable-xor-baseline"}
            and receipt["portable_xor_exact_artifacts"] == len(GENERATED),
            "BM control matrix differs")
    for name, (enabled, checks, code) in {
        "disabled": (False, True, 1), "unchecked": (True, False, 1),
        "portable-xor": (True, True, 0), "portable-xor-baseline": (False, True, 0),
    }.items():
        control = controls[name]
        log_path = root / EXTRACTION / (name + ".log")
        log = log_path.read_text()
        require(control["name"] == name and control["exit_code"] == code
                and control["environment"] == (ENVIRONMENT if enabled else {})
                and ("-checks" in control["command"]) == checks
                and sha(log_path) == control["log_sha256"] and "BM-" not in log
                and (code == 0 or "PrePasses.ml, line 575" in log),
                "BM control evidence differs: " + name)
    audit = receipt["axiom_audit"]
    audit_source = root / EXTRACTION / "Axioms.lean"
    audit_log = root / EXTRACTION / "axioms.log"
    require(audit["exit_code"] == 0 and sha(audit_source) == audit["source_sha256"]
            and sha(audit_log) == audit["log_sha256"]
            and audit_log.read_text().splitlines() == [
                f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
                for name in ("bulksketch.decode.bm.locator", "Aeneas.Std.BmLocatorRuntime.inclusiveRange",
                             "Aeneas.Std.BmLocatorRuntime.reverseIterator")
            ], "BM definition and scoped binding axiom evidence differs")
    raw, retained = project(root)
    return {"raw_generated_file": str(raw.relative_to(root)), "raw_file_sha256": sha(raw),
            "compiled_projection": COMPILED, "projection_file_sha256": sha(root / COMPILED),
            "source_declarations_retained_verbatim": len(retained),
            "shared_types_and_function_dictionary_declarations_checked": True,
            "shared_declarations_checked": len(TYPES) + len(SHARED_FUNCTIONS),
            "native_item_id": NATIVE_ID, "native_body_proof_credit": 0, "translator_variant": VARIANT,
            "generated_declarations": ["bulksketch." + name for name in retained]}


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
