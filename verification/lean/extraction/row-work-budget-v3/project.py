#!/usr/bin/env python3
"""Check the exact original V3 row budget and its explicit V2 sum binding."""

import argparse
from hashlib import sha256
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
RAW = Path("extraction/row-work-budget-v1/Arithmetic/Funs.lean")
RECEIPT = Path("extraction/row-work-budget-v1/receipt.json")
ACTIVE = Path("bridge/Arithmetic/RowWorkBudgetV3Generated.lean")
MARK = "/-- [bulksketch::decode::work::{bulksketch::decode::work::WorkScheduleV3}::row_bound]"
END = "end bulksketch"
HEADER = """-- Original checked V3 row wrapper carrying the V2 sum-cost parameter.
import Arithmetic.RowWorkBudgetV2Generated
import Arithmetic.MaxAffineDegreeGenerated

open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
noncomputable section
namespace bulksketch

"""


def require(condition, message):
    if not condition:
        raise ValueError(message)


def check(root=ROOT, active=None):
    active = root / ACTIVE if active is None else active
    raw = (root / RAW).read_bytes()
    receipt = json.loads((root / RECEIPT).read_text())
    require(receipt["status"] == "generated" and receipt["exit_codes"] == [0, 0]
            and receipt["opaque"] == ["bulksketch::decode::work::sum_costs"]
            and sha256(raw).hexdigest() == receipt["artifacts"]["Arithmetic/Funs.lean"],
            "row budget raw capture differs: " + str(RAW))
    stock = raw.decode()
    begin = stock.index(MARK)
    end = stock.index(END, begin)
    body = stock[begin:end].strip()
    require(body.count("  (capacity : Std.Usize)") == 1 and
            body.count("decode.work.WorkScheduleV2.row_bound capacity") == 1, "V3 sum forwarding differs")
    body = body.replace("  (capacity : Std.Usize)",
                        "  (sumCosts : RowWorkBudgetRuntime.SumCosts) (capacity : Std.Usize)")
    body = body.replace("decode.work.WorkScheduleV2.row_bound capacity",
                        "decode.work.WorkScheduleV2.row_bound sumCosts capacity")
    require(active.read_text() == HEADER + body + "\n\nend bulksketch\n", "active original V3 row body changed")
    return {
        "generated_declarations": ["bulksketch.decode.work.WorkScheduleV3.row_bound"],
        "source_declarations_retained_with_explicit_callee": 1,
        "raw_generated_file": str(RAW),
        "compiled_projection": str(ACTIVE),
        "raw_file_sha256": sha256(raw).hexdigest(),
        "projection_file_sha256": sha256(active.read_bytes()).hexdigest(),
        "source_span": "src/decode/work.rs:332:4-384:5",
        "shared_types_and_function_dictionary_declarations_checked": True,
        "explicit_callee_parameters": ["sumCosts"],
        "native_source_edited": False,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--active", type=Path)
    args = parser.parse_args()
    print(json.dumps(check(args.root, args.active), indent=2))
