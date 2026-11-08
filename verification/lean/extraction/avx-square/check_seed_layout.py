#!/usr/bin/env python3
"""Verify the capture-specific physical RawProduct layout used by the seed model."""
import json
from copy import deepcopy
from pathlib import Path

from project import DIRECTORY, ROOT, TARGET, check as check_square, require, sha

RAW_PRODUCT = ["bulksketch", "types", "RawProduct"]


def chosen_usize(layout_entry):
    constant = layout_entry["chosen"]["Value"][1]["Constant"]["Value"][1][0]
    kind, value = constant["Integer"]["Unsigned"]
    require(kind == "Usize", "AVX seed layout uses a non-usize constant")
    return int(value)


def check_layout(crate):
    targets = crate["target_information"]
    require(len(targets) == 1 and targets[0]["key"] == TARGET, "AVX seed target differs")
    target = targets[0]["value"]
    require(
        target["arch"] == "X86_64" and target["target_pointer_size"] == 8
        and target["is_little_endian"] is True,
        "AVX seed target is not little-endian 64-bit x86",
    )
    declarations = [
        item for item in crate["type_decls"]
        if item and [part.get("Ident", [""])[0] for part in item["item_meta"]["name"]] == RAW_PRODUCT
    ]
    require(len(declarations) == 1, "AVX seed RawProduct declaration differs")
    raw = declarations[0]
    fields = [field["name"] for field in raw["kind"]["Struct"]]
    require(fields == ["lo", "hi"], "AVX seed RawProduct fields differ")
    layouts = raw["layout"]
    require(len(layouts) == 1 and layouts[0]["key"] == TARGET, "AVX seed RawProduct target layout differs")
    layout = layouts[0]["value"]
    variants = layout["variant_layouts"]
    require(len(variants) == 1, "AVX seed RawProduct is not a single-layout struct")
    offsets = [field["chosen"] for field in variants[0]["field_offsets"]]
    size, align = chosen_usize(layout["size"]), chosen_usize(layout["align"])
    require((size, align, offsets) == (16, 8, [0, 8]), "AVX seed RawProduct chosen layout differs")
    return {"stride_bytes": size, "alignment_bytes": align, "lo_bytes": offsets[0], "hi_bytes": offsets[1]}


def rejected_controls(crate):
    controls = [
        ("big-endian", "is_little_endian", False),
        ("narrow-word", "target_pointer_size", 4),
    ]
    rejected = []
    for label, field, value in controls:
        model = deepcopy(crate)
        model["target_information"][0]["value"][field] = value
        try:
            check_layout(model)
        except ValueError:
            rejected.append(label)
        else:
            raise ValueError("AVX seed target control was accepted: " + label)
    model = deepcopy(crate)
    raw = next(item for item in model["type_decls"] if item and
               [part.get("Ident", [""])[0] for part in item["item_meta"]["name"]] == RAW_PRODUCT)
    offsets = raw["layout"][0]["value"]["variant_layouts"][0]["field_offsets"]
    offsets[1]["chosen"] = 0
    try:
        check_layout(model)
    except ValueError:
        rejected.append("overlapping-raw-words")
    else:
        raise ValueError("AVX seed overlapping RawProduct fields accepted")
    return rejected


def check(root: Path = ROOT):
    check_square(root)
    llbc = root / DIRECTORY / "arithmetic.llbc"
    crate = json.loads(llbc.read_text())["translated"]
    layout = check_layout(crate)
    require(
        (root.parents[1] / "src/types.rs").read_text() ==
        next(file["contents"] for file in crate["files"] if file and file["name"] == {"Local": "src/types.rs"}),
        "AVX seed RawProduct source differs",
    )
    return {
        "target": TARGET,
        "llbc_sha256": sha(llbc),
        "captured_raw_product": layout,
        "rejected_layout_controls": rejected_controls(crate),
        "rust_layout_guarantee": False,
        "compiler_instruction_correspondence_proved": False,
    }


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
