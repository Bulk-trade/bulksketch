#!/usr/bin/env python3
"""Check the original V1 row_bound body and its sole explicit callee slot."""

import argparse
import json
from pathlib import Path

import hashlib
import re

ROOT = Path(__file__).resolve().parents[2]
EXTRACTION = Path("extraction/row-work-budget-v1")
ACTIVE = Path("bridge/Arithmetic/RowWorkBudgetGenerated.lean")
ROOTS_RAW = Path("extraction/root-work-budget/Arithmetic/Funs.lean")
SCHEDULE = Path("bridge/Arithmetic/WorkScheduleGenerated.lean")
ARTIFACTS = {
    "arithmetic.llbc", "charon.log", "aeneas.log", "Arithmetic/Funs.lean",
    "Arithmetic/Types.lean", "Arithmetic/FunsExternal_Template.lean",
}

SELECTOR = "bulksketch::decode::work::_::row_bound"
OPAQUE = "bulksketch::decode::work::sum_costs"
ROW = "decode.work.WorkScheduleV1.row_bound"
ROOTS = "decode.work.WorkScheduleV1.roots_bound"
SLOT = "  (sumCosts : RowWorkBudgetRuntime.SumCosts) (capacity : Std.Usize)"
SOURCE = "  (capacity : Std.Usize)"
CALL = "let r ← sumCosts s"
HEADER = '-- Checked original row_bound projection with the explicit captured sum_costs slot.\nimport Arithmetic.RootWorkBudgetGenerated\n\nopen Aeneas Aeneas.Std Result ControlFlow Error\nset_option maxHeartbeats 1000000\nset_option maxRecDepth 2048\n\nnamespace Aeneas.Std.RowWorkBudgetRuntime\n\nabbrev SumCosts := Slice bulksketch.decode.work.Charge →\n  Result (core.result.Result U64 bulksketch.types.DecodeError)\n\nend Aeneas.Std.RowWorkBudgetRuntime\n\nnoncomputable section\n\nnamespace bulksketch\n\nvariable (sumCosts : RowWorkBudgetRuntime.SumCosts)\nlocal notation "decode.work.sum_costs" => sumCosts\n\n'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def blocks(path):
    body = path.read_text().split("namespace bulksketch\n", 1)[1].rsplit("end bulksketch", 1)[0]
    declarations = {}
    for block in re.findall(r"(?ms)^/--.*?(?=^/--|\Z)", body):
        names = re.findall(r"(?m)^(?:def|inductive|structure|abbrev)\s+(\S+)", block)
        require(len(names) == 1 and names[0] not in declarations, "unexpected declaration in " + str(path))
        declarations[names[0]] = block.strip()
    return declarations


def check(root=ROOT, active=None):
    evidence = root / EXTRACTION
    active = root / ACTIVE if active is None else active
    receipt = json.loads((evidence / "receipt.json").read_text())
    root_receipt = json.loads((root / "extraction/root-work-budget/receipt.json").read_text())
    require(receipt["status"] == "generated" and receipt["exit_codes"] == [0, 0]
            and receipt["selected_roots"] == [SELECTOR] and receipt["opaque"] == [OPAQUE]
            and set(receipt["artifacts"]) == ARTIFACTS, "row source receipt changed")
    require(all(receipt[key] == root_receipt[key] for key in (
        "source_commit", "rust_toolchain", "target", "charon_commit", "aeneas_commit", "tool_binary_sha256",
    )), "row source or toolchain changed")
    for file, digest in receipt["artifacts"].items():
        require(sha(evidence / file) == digest, "raw row capture changed: " + str(EXTRACTION / file))
    llbc = json.loads((evidence / "arithmetic.llbc").read_text())
    options = llbc["translated"]["options"]
    require(llbc["has_errors"] is False and options["start_from"] == [SELECTOR]
            and options["opaque"] == [OPAQUE], "row source or callee scope changed")
    generated = blocks(evidence / "Arithmetic/Funs.lean")
    compiled = blocks(active)
    active_header = active.read_text().split("/-- [bulksketch::decode::work::", 1)[0]
    require(active_header == HEADER, "row runtime binding changed")
    require(set(compiled) == {ROW}, "unexpected active row declaration")
    row = compiled[ROW]
    require(row == generated[ROW], "active original row body changed")
    types = blocks(evidence / "Arithmetic/Types.lean")
    roots_types = blocks(root / "extraction/work-schedule/Arithmetic/Types.lean")
    for name in ("decode.work.Charge", "types.WorkUnits", "types.DecodeError"):
        require(types[name] == roots_types[name], "row native type changed: " + name)
    root_capture = blocks(root / ROOTS_RAW)
    schedule = blocks(root / SCHEDULE)
    require(generated[ROOTS] == root_capture[ROOTS], "row root-bound callee changed")
    for operation in ("number", "add", "mul", "WorkScheduleV1.cost"):
        name = "decode.work." + operation
        require(generated[name] == schedule[name], "row native price callee changed: " + name)
    return {
        "generated_declarations": ["bulksketch." + ROW],
        "source_declarations_retained_verbatim": 1,
        "shared_types_and_function_dictionary_declarations_checked": True,
        "raw_generated_file": str(EXTRACTION / "Arithmetic/Funs.lean"),
        "compiled_projection": str(ACTIVE),
        "source_span": "src/decode/work.rs:230:4-258:5",
        "explicit_callee": OPAQUE,
        "raw_file_sha256": sha(evidence / "Arithmetic/Funs.lean"),
        "projection_file_sha256": sha(active),
        "native_source_edited": False,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--active", type=Path, default=None)
    args = parser.parse_args()
    print(json.dumps(check(args.root, args.active), indent=2))
