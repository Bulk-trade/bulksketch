#!/usr/bin/env python3
"""Check the original affine maximum const and its generated loop."""

import argparse
from hashlib import sha256
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
RAW = Path("extraction/row-work-budget-v1/Arithmetic/Funs.lean")
RECEIPT = Path("extraction/row-work-budget-v1/receipt.json")
ACTIVE = Path("bridge/Arithmetic/MaxAffineDegreeGenerated.lean")
MARK = "/-- [bulksketch::decode::affine::MAX_PREFERRED_DEGREE]: loop body 0:"
END = "/-- [bulksketch::decode::work::log2_ceil]"
HEADER = """-- Exact original generated maximum preferred degree and loop.
import BulksketchBridge.AffinePredictor

open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace bulksketch

"""


def require(condition, message):
    if not condition:
        raise ValueError(message)


def declaration(text, name):
    for block in re.findall(r"(?ms)^/--.*?(?=^/--|\Z)", text):
        if re.search(r"(?m)^def\s+" + re.escape(name) + r"\b", block):
            return block.strip()
    raise ValueError("missing declaration " + name)


def check(root=ROOT, active=None):
    active = root / ACTIVE if active is None else active
    raw = (root / RAW).read_bytes()
    receipt = json.loads((root / RECEIPT).read_text())
    require(receipt["status"] == "generated" and receipt["exit_codes"] == [0, 0]
            and receipt["opaque"] == ["bulksketch::decode::work::sum_costs"]
            and sha256(raw).hexdigest() == receipt["artifacts"]["Arithmetic/Funs.lean"],
            "maximum degree raw capture differs: " + str(RAW))
    stock = raw.decode()
    begin = stock.index(MARK)
    end = stock.index(END, begin)
    require(active.read_text() == HEADER + stock[begin:end].strip() + "\n\nend bulksketch\n",
            "active original affine maximum body changed")
    for file, name in (
        ("bridge/Arithmetic/RootSetupGenerated.lean", "decode.affine.preferred"),
        ("bridge/Arithmetic/Funs.lean", "field.Gf64.Insts.BulksketchFieldBinaryField"),
    ):
        require(declaration(stock, name) == declaration((root / file).read_text(), name),
                "shared original affine selection changed: " + name)
    return {
        "generated_declarations": [
            "bulksketch.decode.affine.MAX_PREFERRED_DEGREE_loop.body",
            "bulksketch.decode.affine.MAX_PREFERRED_DEGREE_loop",
            "bulksketch.decode.affine.MAX_PREFERRED_DEGREE",
        ],
        "source_declarations_retained_verbatim": 3,
        "raw_generated_file": str(RAW),
        "compiled_projection": str(ACTIVE),
        "raw_file_sha256": sha256(raw).hexdigest(),
        "projection_file_sha256": sha256(active.read_bytes()).hexdigest(),
        "source_span": "src/decode/affine.rs:70:0-80:2",
        "shared_types_and_function_dictionary_declarations_checked": True,
        "native_source_edited": False,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--active", type=Path)
    args = parser.parse_args()
    print(json.dumps(check(args.root, args.active), indent=2))
