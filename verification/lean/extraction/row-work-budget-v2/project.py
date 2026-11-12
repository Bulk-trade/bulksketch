#!/usr/bin/env python3
"""Check the exact original V2 row budget and its explicit V1 sum binding."""

import argparse
from hashlib import sha256
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
RAW = Path("extraction/row-work-budget-v1/Arithmetic/Funs.lean")
RECEIPT = Path("extraction/row-work-budget-v1/receipt.json")
ACTIVE = Path("bridge/Arithmetic/RowWorkBudgetV2Generated.lean")
MARK = "/-- [bulksketch::decode::work::{bulksketch::decode::work::WorkScheduleV2}::row_bound]"
END = "/-- [bulksketch::decode::work::{bulksketch::decode::work::WorkScheduleV3}::row_bound]"
HEADER = """-- Original checked V2 row wrapper carrying the V1 sum-cost parameter.
import Arithmetic.RowWorkBudgetGenerated

open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
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
            body.count("decode.work.WorkScheduleV1.row_bound capacity") == 1, "V2 sum forwarding differs")
    body = body.replace("  (capacity : Std.Usize)",
                        "  (sumCosts : RowWorkBudgetRuntime.SumCosts) (capacity : Std.Usize)")
    body = body.replace("decode.work.WorkScheduleV1.row_bound capacity",
                        "decode.work.WorkScheduleV1.row_bound sumCosts capacity")
    require(active.read_text() == HEADER + body + "\n\nend bulksketch\n", "active original V2 row body changed")
    return {
        "generated_declarations": ["bulksketch.decode.work.WorkScheduleV2.row_bound"],
        "source_declarations_retained_with_explicit_callee": 1,
        "explicit_callee_parameters": ["sumCosts"],
        "shared_types_and_function_dictionary_declarations_checked": True,
        "raw_generated_file": str(RAW),
        "compiled_projection": str(ACTIVE),
        "raw_file_sha256": sha256(raw).hexdigest(),
        "projection_file_sha256": sha256(active.read_bytes()).hexdigest(),
        "source_span": "src/decode/work.rs:265:4-290:5",
        "native_source_edited": False,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--active", type=Path)
    args = parser.parse_args()
    print(json.dumps(check(args.root, args.active), indent=2))
