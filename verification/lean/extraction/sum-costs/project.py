#!/usr/bin/env python3
"""Check the original sum source and the exact typed std specialization."""

import argparse
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
EXTRACTION = Path("extraction/sum-costs")
ACTIVE = Path("bridge/Arithmetic/SumCostsGenerated.lean")
VARIANT = "checked-sum-costs-try-fold-v1"
SOURCE = "decode.work.sum_costs"
ARTIFACTS = {
    "arithmetic.llbc", "specialized.llbc", "charon.log", "aeneas.log", "specialize.py",
    "Arithmetic/Types.lean", "Arithmetic/Funs.lean", "Arithmetic/FunsExternal_Template.lean",
}
RUNTIME = {"sumCostsTryFoldFrom", "decode.work.checked_sum_costs_slice_try_fold"}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return sha256(path.read_bytes()).hexdigest()


def blocks(path):
    body = path.read_text().split("namespace bulksketch\n", 1)[1].rsplit("end bulksketch", 1)[0]
    declarations = {}
    for block in re.findall(r"(?ms)^/--.*?(?=^/--|\Z)", body):
        names = re.findall(r"(?m)^(?:noncomputable )?(?:def|inductive|structure|abbrev)\s+(\S+)", block)
        require(len(names) == 1 and names[0] not in declarations, "unexpected declaration in " + str(path))
        declarations[names[0]] = block.strip()
    return declarations


def check(root=ROOT, active=None):
    evidence = root / EXTRACTION
    active = root / ACTIVE if active is None else active
    receipt = json.loads((evidence / "receipt.json").read_text())
    previous = json.loads((root / "extraction/work-schedule/receipt.json").read_text())
    require(receipt["status"] == "generated" and receipt["variant_id"] == VARIANT
            and receipt["exit_codes"] == [0, 0, 0] and set(receipt["artifacts"]) == ARTIFACTS,
            "sum_costs specialization receipt changed")
    require(all(receipt[key] == previous[key] for key in (
        "source_commit", "rust_toolchain", "target", "charon_commit", "aeneas_commit", "tool_binary_sha256",
    )), "sum_costs source or toolchain pin changed")
    ch, transform, aeneas = receipt["commands"]
    replay = receipt["replay"]
    require(ch[1:4] == ["cargo", "--preset=aeneas", "--sysroot=default"]
            and ch[5] == "--start-from=bulksketch::decode::work::sum_costs"
            and transform[:2] == ["python3", "-O"]
            and ch[4].removeprefix("--dest-file=") == transform[-2]
            and transform[-1] == aeneas[-1]
            and aeneas[1:-2] == replay["command"][1:-2] ==
                ["-backend", "lean", "-checks", "-sequential", "-no-progress-bar", "-split-files", "-dest"]
            and replay["exit_code"] == 0 and replay["specialized_sha256"] == receipt["artifacts"]["specialized.llbc"]
            and replay["output_sha256"] == {name: receipt["artifacts"]["Arithmetic/" + name]
                for name in ("Types.lean", "Funs.lean", "FunsExternal_Template.lean")},
            "sum_costs checked specialization and replay commands differ")
    raw = json.loads((evidence / "arithmetic.llbc").read_bytes())
    source = root.parents[1] / "src/decode/work.rs"
    source_files = [file for file in raw["translated"]["files"]
                    if file and file["name"].get("Local") == "src/decode/work.rs"]
    require(raw["has_errors"] is False and raw["translated"]["options"]["skip_borrowck"] is False
            and len(source_files) == 1 and source_files[0]["contents"].encode() == source.read_bytes(),
            "sum_costs frozen Rust source differs")
    for file, digest in receipt["artifacts"].items():
        require(sha(evidence / file) == digest, "sum_costs raw artifact changed: " + str(EXTRACTION / file))
    spec = importlib.util.spec_from_file_location("sum_costs_specialization", evidence / "specialize.py")
    transformer = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(transformer)
    require(transformer.specialize((evidence / "arithmetic.llbc").read_bytes()) ==
            (evidence / "specialized.llbc").read_bytes(), "typed specialization replay differs")

    types = blocks(evidence / "Arithmetic/Types.lean")
    functions = blocks(evidence / "Arithmetic/Funs.lean")
    source_types = {SOURCE + ".closure": types[SOURCE + ".closure"]}
    source_functions = {name: body for name, body in functions.items()
                        if name == SOURCE or name.startswith(SOURCE + ".closure.Insts.")}
    require(len(source_functions) == 5, "sum_costs source declaration set changed")
    compiled = blocks(active)
    require(set(compiled) == set(source_types) | set(source_functions) | RUNTIME,
            "active sum_costs declarations changed")
    require(all(compiled[name] == body for name, body in (source_types | source_functions).items()),
            "active sum_costs source body changed")
    require(all(sha256(compiled[name].encode()).hexdigest() == receipt["runtime"][name] for name in RUNTIME),
            "specialized iterator model changed")
    header = active.read_text().split("/-- [bulksketch::decode::work::sum_costs", 1)[0]
    require(sha256(header.encode()).hexdigest() == receipt["header_sha256"], "active sum_costs imports changed")
    schedule = blocks(root / "bridge/Arithmetic/WorkScheduleGenerated.lean")
    require(all(functions[name] == schedule[name] for name in (
        "decode.work.add", "decode.work.WorkScheduleV1.cost",
    )), "reused native sum pricing changed")
    return {
        "translator_variant": VARIANT,
        "shared_types_and_function_dictionary_declarations_checked": True,
        "raw_generated_file": str(EXTRACTION / "Arithmetic/Funs.lean"),
        "compiled_projection": str(ACTIVE),
        "source_span": "src/decode/work.rs:314:0-318:1",
        "source_declarations_retained_verbatim": len(source_functions),
        "source_type_declarations_retained_verbatim": len(source_types),
        "generated_declarations": ["bulksketch." + name for name in source_functions],
        "explicit_std_model": "core::iter::traits::iterator::Iterator::try_fold on shared Slice<Charge>",
        "raw_file_sha256": sha(evidence / "Arithmetic/Funs.lean"),
        "projection_file_sha256": sha(active),
        "native_source_edited": False,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--active", type=Path)
    args = parser.parse_args()
    print(json.dumps(check(args.root, args.active), indent=2))
