#!/usr/bin/env python3
"""Check the original stock roots_bound projection and reused declarations."""

import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
EXTRACTION = Path("extraction/root-work-budget")
ACTIVE = Path("bridge/Arithmetic/RootWorkBudgetGenerated.lean")
ARTIFACTS = {
    "arithmetic.llbc", "charon.log", "aeneas.log", "Arithmetic/Funs.lean",
    "Arithmetic/Types.lean", "Arithmetic/FunsExternal_Template.lean",
}
SELECTOR = "bulksketch::decode::work::_::roots_bound"
NAME = "decode.work.WorkScheduleV1.roots_bound"
PIN = "0a5bda53f6b07fcae8acd870e2d0c4a246d207e6"
HEADER = """-- Scoped projection of the checked original WorkScheduleV1::roots_bound declaration.
import Arithmetic.WorkScheduleGenerated

open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

noncomputable section

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
        names = re.findall(r"(?m)^(?:def|inductive|structure|abbrev)\s+(\S+)", block)
        require(len(names) == 1 and names[0] not in declarations, "unexpected declaration in " + str(path))
        declarations[names[0]] = block.strip()
    return declarations


def check(root=ROOT, active=None):
    evidence = root / EXTRACTION
    active = root / ACTIVE if active is None else active
    receipt = json.loads((evidence / "receipt.json").read_text())
    require(receipt["status"] == "generated" and receipt["source_commit"] == PIN
            and receipt["selected_roots"] == [SELECTOR] and receipt["exit_codes"] == [0, 0]
            and set(receipt["artifacts"]) == ARTIFACTS,
            "wrong source pin or selector")
    schedule_receipt = json.loads((root / "extraction/work-schedule/receipt.json").read_text())
    require(all(receipt[key] == schedule_receipt[key] for key in (
        "source_commit", "rust_toolchain", "target", "charon_commit", "aeneas_commit", "tool_binary_sha256",
    )), "source or toolchain differs from the pinned work-schedule capture")
    for file, expected in receipt["artifacts"].items():
        require(sha(evidence / file) == expected, "raw artifact changed: " + str(EXTRACTION / file))
    llbc = json.loads((evidence / "arithmetic.llbc").read_text())
    translated = llbc["translated"]
    options = translated["options"]
    targets = translated["target_information"]
    require(llbc["has_errors"] is False and options["start_from"] == [SELECTOR] and options["opaque"] == [],
            "wrong LLBC capture")
    require(len(targets) == 1 and targets[0]["key"] == "x86_64-apple-darwin"
            and targets[0]["value"]["target_pointer_size"] == 8, "wrong capture target")
    raw = blocks(evidence / "Arithmetic/Funs.lean")
    types = blocks(evidence / "Arithmetic/Types.lean")
    stock_root = raw.pop(NAME)
    bridge = root / "bridge"
    schedule = blocks(bridge / "Arithmetic/WorkScheduleGenerated.lean")
    shared_types = blocks(bridge / "Workmeter/Types.lean") | schedule
    require(set(raw) == {
        "decode.work.mul", "decode.work.add", "decode.work.number",
        "decode.work.number.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorDecodeError.call_once",
        "decode.work.number.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorDecodeError",
    }, "unexpected native roots dependencies")
    require(all(body == schedule.get(name) for name, body in raw.items()), "native source helper changed")
    require(all(body == shared_types.get(name) for name, body in types.items()), "native shared type changed")
    require(active.read_text() == HEADER + stock_root + "\n\nend bulksketch\n", "active root body changed")
    return {
        "source": "src/decode/work.rs",
        "raw_generated_file": str(EXTRACTION / "Arithmetic/Funs.lean"),
        "compiled_projection": str(ACTIVE),
        "rust_span": "204:4-227:5",
        "source_declarations_retained_verbatim": 1,
        "shared_types_and_function_dictionary_declarations_checked": True,
        "generated_declarations": ["bulksketch." + NAME],
        "raw_file_sha256": sha(evidence / "Arithmetic/Funs.lean"),
        "projection_file_sha256": sha(active),
        "shared_work_functions_checked": sorted(raw),
        "shared_work_types_checked": sorted(types),
        "native_source_edited": False,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--active", type=Path, default=None)
    args = parser.parse_args()
    print(json.dumps(check(args.root, args.active), indent=2))
