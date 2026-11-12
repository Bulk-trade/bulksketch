#!/usr/bin/env python3
"""Check the original work schedule and execution charge projection."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
EXTRACTION = Path("extraction/work-schedule")
RAW = EXTRACTION / "Arithmetic"
ACTIVE = Path("bridge/Arithmetic/WorkScheduleGenerated.lean")
RUNTIME = Path("bridge/Arithmetic/WorkScheduleRuntime.lean")
ROOTS = ["bulksketch::decode::work::_::cost", "bulksketch::decode::stages::_::charge"]
TYPES = ["decode.work.number.closure", "decode.work.WorkScheduleV1.cost.closure", "decode.work.Charge"]
FUNCTIONS = ["decode.work." + name for name in (
    "log2_ceil", "mul", "add", "number.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorDecodeError.call_once",
    "number.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorDecodeError", "number", "square", "square_mod",
    "WorkScheduleV1.cost.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorDecodeError.call_once",
    "WorkScheduleV1.cost.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorDecodeError", "WorkScheduleV1.cost",
)] + ["decode.stages.Execution.charge"]
ARTIFACTS = {str(EXTRACTION / name) for name in (
    "arithmetic.llbc", "charon.log", "aeneas.log", "Arithmetic/Funs.lean", "Arithmetic/Types.lean",
    "Arithmetic/FunsExternal_Template.lean",
)}
HEADER = """-- Exact original-source declaration projection. Imports are adapted only.
module
public import Workmeter.Funs
public import Arithmetic.SliceKernelTypes
public import Arithmetic.WorkScheduleRuntime
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

"""


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def blocks(path):
    body = path.read_text().split("namespace bulksketch\n", 1)[1].rsplit("end bulksketch", 1)[0]
    declarations = {}
    for block in re.findall(r"(?ms)^/--.*?(?=^/--|\Z)", body):
        names = re.findall(r"(?m)^(?:def|impl_def|inductive|structure|abbrev)\s+(\S+)", block)
        require(len(names) == 1 and names[0] not in declarations, "unexpected work declaration in " + str(path))
        declarations[names[0]] = block.strip()
    return declarations


def check(root=ROOT):
    receipt = json.loads((root / EXTRACTION / "receipt.json").read_text())
    require(receipt["status"] == "generated" and receipt["selected_roots"] == ROOTS and
            receipt["llbc_has_errors"] is False and set(receipt["artifacts"]) == ARTIFACTS,
            "invalid work schedule extraction receipt")
    for path, digest in receipt["artifacts"].items():
        require(sha(root / path) == digest, "raw work schedule artifact differs: " + path)
    llbc_path = root / EXTRACTION / "arithmetic.llbc"
    llbc = json.loads(llbc_path.read_text())
    translated = llbc["translated"]
    require(sha(llbc_path) == receipt["llbc_sha256"] and llbc["has_errors"] is False and
            translated["options"]["start_from"] == ROOTS and translated["options"]["opaque"] == [],
            "work schedule LLBC root or body changed")
    targets = translated["target_information"]
    require(len(targets) == 1 and targets[0]["key"] == "x86_64-apple-darwin" and
            targets[0]["value"]["target_pointer_size"] == 8, "unexpected work schedule target")
    types = blocks(root / RAW / "Types.lean")
    shared_types = {}
    for path in ("Workmeter/Types.lean", "Arithmetic/Types.lean", "Arithmetic/SliceKernelTypes.lean"):
        shared_types.update(blocks(root / "bridge" / path))
    require([name for name in types if name in TYPES] == TYPES and
            all(types[name] == shared_types.get(name) for name in types if name not in TYPES),
            "shared work schedule type differs")
    functions = blocks(root / RAW / "Funs.lean")
    shared_functions = blocks(root / "bridge/Workmeter/Funs.lean")
    require(all(block == shared_functions.get(name) for name, block in functions.items()
                if name.startswith("types.WorkMeter.charge")), "shared WorkMeter charge differs")
    require([name for name in functions if name.startswith("decode.work.") or
             name == "decode.stages.Execution.charge"] == FUNCTIONS, "work schedule declaration set changed")
    declarations = {name: types[name] for name in TYPES} | {name: functions[name] for name in FUNCTIONS}
    for name, block in declarations.items():
        require(hashlib.sha256(block.encode()).hexdigest() == receipt["matching_filtered_declarations"][name],
                "work schedule differs from the filtered reconstruct extraction: " + name)
    projection = HEADER + "".join(block + "\n\n" for block in declarations.values()) + "end bulksketch\n"
    require((root / ACTIVE).read_text() == projection, "compiled work schedule projection differs")
    return {
        "raw_generated_file": str(RAW / "Funs.lean"), "raw_file_sha256": sha(root / RAW / "Funs.lean"),
        "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
        "source_declarations_retained_verbatim": len(FUNCTIONS),
        "source_type_declarations_retained_verbatim": len(TYPES),
        "shared_types_and_function_dictionary_declarations_checked": True,
        "generated_declarations": ["bulksketch." + name for name in FUNCTIONS],
        "runtime_sha256": sha(root / RUNTIME), "native_source_edited": False,
    }


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
