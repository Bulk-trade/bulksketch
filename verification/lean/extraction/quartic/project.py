#!/usr/bin/env python3
"""Check the exact original quartic and solve projection and checked translator evidence."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/quartic")
RAW = DIRECTORY / "Arithmetic"
ACTIVE = Path("bridge/Arithmetic/QuarticGenerated.lean")
SELECTOR = "bulksketch::decode::deg34::solve"
VARIANT = "checked-fixedpoint-scalar-array-loan-retry-v1"
SOURCE = Path("src/decode/deg34.rs")
SOURCE_SHA = "50e92cc158d33b58361cf95719d4f13e01295802a15e1dab7622fab5ce050015"
NAMES = ["decode.deg34." + suffix for suffix in
         ("quartic_loop0.body", "quartic_loop0", "quartic_loop1.body", "quartic_loop1", "quartic", "solve")]
SHARED_TYPES = ("Types.lean", "SliceKernelTypes.lean", "CertificateGenerated.lean")
SHARED_FUNCTIONS = {
    "AffineQuarticGenerated.lean": ("Shared0A.Insts.CoreCmpEq", "Shared0A.Insts.CoreCmpOrd", "decode.deg34.affine_quartic"),
    "CubicGenerated.lean": ("decode.deg34.OMEGA", "decode.deg34.quadratic", "decode.deg34.cubic"),
    "CubeRootGenerated.lean": tuple("decode.deg34." + suffix for suffix in
                                    ("cube_root_loop.body", "cube_root_loop", "cube_root")),
    "CertificateGenerated.lean": tuple("decode.deg34." + suffix for suffix in
        ("certificate", "certificate_loop0.body", "certificate_loop0", "certificate_loop0_loop0.body",
         "certificate_loop0_loop0", "certificate.closure.Insts.CoreOpsFunctionFnMutTuplePairUsizeShared0U64Bool",
         "certificate.closure.Insts.CoreOpsFunctionFnMutTuplePairUsizeShared0U64Bool.call_mut",
         "certificate.closure.Insts.CoreOpsFunctionFnOnceTuplePairUsizeShared0U64Bool",
         "certificate.closure.Insts.CoreOpsFunctionFnOnceTuplePairUsizeShared0U64Bool.call_once")),
}
ARTIFACTS = {str(DIRECTORY / path) for path in (
    "arithmetic.llbc", "charon.log", "aeneas.log", "pinned.log", "unchecked.log", "Arithmetic/Funs.lean",
    "Arithmetic/FunsExternal_Template.lean", "Arithmetic/Types.lean", "translator/checked-array-loan-retry.patch",
    "translator/array-loan-retry-delta.patch", "translator/controls.log", "translator/guards/array_loan_controls.ml",
    "translator/guards/dune", "translator/narrow.log", "translator/cubic-control.log",
    "translator/certificate-control.log")}
HEADER = """-- Exact original-source declaration projection. The imports reuse checked dependencies.
module
public import Arithmetic.AffineQuarticGenerated
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

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


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    require(receipt["status"] == "checked_original_closure_extracted" and receipt["selector"] == SELECTOR
            and receipt["candidate_variant"] == VARIANT and receipt["native_source_edited"] is False
            and receipt["llbc_has_errors"] is False, "invalid quartic extraction receipt")
    require(set(receipt["files_sha256"]) == ARTIFACTS, "incomplete quartic artifact set")
    for path, expected in receipt["files_sha256"].items():
        require(sha(root / path) == expected, "quartic artifact differs: " + path)
    require(sha(root.parents[1] / SOURCE) == SOURCE_SHA, "frozen quartic Rust source differs")
    llbc = json.loads((root / DIRECTORY / "arithmetic.llbc").read_text())
    translated = llbc["translated"]
    require(llbc["has_errors"] is False and translated["options"]["start_from"] == [SELECTOR]
            and translated["options"]["opaque"] == [], "quartic LLBC closure differs")
    target = translated["target_information"]
    require(len(target) == 1 and target[0]["key"] == "x86_64-apple-darwin"
            and target[0]["value"]["target_pointer_size"] == 8, "unexpected quartic target")
    for suffix, lines in (("quartic", (162, 195)), ("solve", (198, 215))):
        path = [{"Ident": [part, 0]} for part in ("bulksketch::decode::deg34::" + suffix).split("::")]
        matching = [fn for fn in translated["fun_decls"] if fn and fn["item_meta"]["name"] == path]
        require(len(matching) == 1 and "Structured" in matching[0]["body"], "quartic or solve LLBC body missing")
        span = matching[0]["item_meta"]["span"]["Untagged"]["data"]
        source = translated["files"][span["file_id"]]
        require((span["beg"]["line"], span["end"]["line"]) == lines and source["name"] == {"Local": str(SOURCE)}
                and hashlib.sha256(source["contents"].encode()).hexdigest() == SOURCE_SHA,
                "quartic LLBC source span or contents differ")
    commands = {entry["name"]: entry for entry in receipt["commands"]}
    require(set(commands) == {"charon", "candidate-build", "narrow", "replay", "unchecked", "pinned",
                              "cubic-control", "certificate-control", "guard-controls"}
            and commands["replay"]["exit_code"] == 0
            and {"-checks", "-sequential"} <= set(commands["replay"]["command"])
            and commands["pinned"]["exit_code"] == commands["unchecked"]["exit_code"] == 1
            and "-checks" not in commands["unchecked"]["command"]
            and len(receipt["guard_controls"]) == len(set(receipt["guard_controls"])) == 8,
            "quartic translator controls differ")
    functions = declarations(root / RAW / "Funs.lean")
    for filename, names in SHARED_FUNCTIONS.items():
        shared = declarations(root / "bridge/Arithmetic" / filename)
        require(all(functions[name] == shared[name] for name in names), "shared quartic declaration differs: " + filename)
    types = declarations(root / RAW / "Types.lean")
    shared = {}
    for filename in SHARED_TYPES:
        shared.update(declarations(root / "bridge/Arithmetic" / filename))
    require(len(types) == 7 and all(block == shared[name] for name, block in types.items()), "shared quartic types differ")
    require([name for name in functions if name in NAMES] == NAMES, "quartic projection declaration set differs")
    projected = HEADER + "\n\n".join(functions[name] for name in NAMES) + "\n\nend bulksketch\n"
    require((root / ACTIVE).read_text() == projected, "compiled quartic projection differs")
    return {
        "raw_generated_file": str(RAW / "Funs.lean"), "raw_file_sha256": sha(root / RAW / "Funs.lean"),
        "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
        "source_declarations_retained_verbatim": len(NAMES),
        "shared_types_and_function_dictionary_declarations_checked": True,
        "generated_declarations": ["bulksketch." + name for name in NAMES],
        "translator_variant": VARIANT, "native_source_edited": False,
    }


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
