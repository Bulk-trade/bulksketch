#!/usr/bin/env python3
"""Project the frozen AVX XOR caller's exact validated loop into Lean."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
EXTRACTION = "extraction/avx-xor-assign"
GENERATED = "bridge/BulksketchBridge/AvxXorLlbcGenerated.lean"
SOURCE = "src/backend/x86_vpclmul512.rs"
SOURCE_SHA = "7a9c29dff254508671aa4122b20644b21a9cfb40f86ba5eaadce02bf680475d4"
LLBC_SHA = "e45bb1164507f4d66a98db52107ecdd9fc4949ae4b2c34d516a7323a40177140"
# The decoded operands below are excluded. Everything else is bound, including
# local types, trait resolution, callee identities, lifetime actions, the
# reborrow/metadata/Option projections, cleanup, loop edges and terminal Unit.
STRUCTURE_SHA = "36d72ad268a4e2f8a89ccbc19c260b649a1986bb9a3f67dd7062d4597c6bde75"
CHUNKS = {14: (6, 37), 24: (8, 39)}
CALLS = {
    78: ("loadLeft", ((19, 59),)),
    88: ("loadRight", ((21, 60),)),
    95: ("xor", ((18, 58), (20, 58))),
    103: ("store", ((16, 57), (17, 58))),
}
FILES = {"arithmetic.llbc", "charon.log", "aeneas.log", "Arithmetic/Funs.lean",
         "Arithmetic/Types.lean", "Arithmetic/FunsExternal_Template.lean",
         "Arithmetic/TypesExternal_Template.lean"}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def require(valid, message):
    if not valid:
        raise ValueError(message)


def move(slot, ty):
    return {"Move": {"kind": {"Local": slot}, "ty": {"Deduplicated": ty}}}


def blocks(document):
    decls = document["translated"]["fun_decls"]
    outer = decls[11]["body"]["Structured"]["body"]["statements"]
    inner, = [stmt["kind"]["Loop"]["statements"] for stmt in outer if stmt["id"] == 115]
    return outer, inner


def constant_usize(document, index):
    values = set()

    def visit(node):
        if isinstance(node, dict):
            entry = node.get("Value")
            if isinstance(entry, list) and len(entry) == 2 and entry[0] == index:
                value = entry[1]
                if isinstance(value, list) and len(value) == 2 and value[1] == {"Deduplicated": 0}:
                    literal = value[0].get("Integer", {}).get("Unsigned")
                    if isinstance(literal, list) and literal[0] == "Usize":
                        values.add(int(literal[1]))
            for value in node.values():
                visit(value)
        elif isinstance(node, list):
            for value in node:
                visit(value)

    visit(document)
    require(len(values) == 1, "unresolved usize chunk width")
    return values.pop()


def projection(document, source):
    require(document["has_errors"] is False and sha(source.encode()) == SOURCE_SHA,
            "invalid LLBC or Rust source pin")
    target, = document["translated"]["target_information"]
    require(target["key"] == "x86_64-apple-darwin" and target["value"]["is_little_endian"] is True
            and target["value"]["target_pointer_size"] == 8, "unexpected target")
    file = document["translated"]["files"][6]
    require(file["name"] == {"Local": SOURCE} and file["contents"] == source,
            "LLBC source file mismatch")
    decls = document["translated"]["fun_decls"]
    lines = source.splitlines(keepends=True)
    for id in (11, 25, 27, 121):
        span = decls[id]["item_meta"]["span"]["Untagged"]["data"]
        begin, end = span["beg"], span["end"]
        rust = (lines[begin["line"] - 1][begin["col"]:] + "".join(lines[begin["line"]:end["line"] - 1])
                + lines[end["line"] - 1][:end["col"]])
        require(span["file_id"] == 6 and rust == decls[id]["item_meta"]["source_text"],
                "LLBC source span mismatch")
    frozen = deepcopy(document)
    for block, decoded in zip(blocks(frozen), (CHUNKS, CALLS)):
        for statement in block:
            if statement["id"] in decoded:
                statement["kind"]["Call"]["call"]["args"] = []
    canon = json.dumps(frozen, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()
    require(sha(canon) == STRUCTURE_SHA, "frozen LLBC structure or metadata changed")
    outer, inner = blocks(document)
    widths = []
    for stmt in outer:
        if stmt["id"] in CHUNKS:
            borrowed, width = stmt["kind"]["Call"]["call"]["args"]
            require(borrowed == move(*CHUNKS[stmt["id"]])
                    and width == {"Const": {"Deduplicated": 8}}, "changed chunks operand")
            widths.append(constant_usize(document, width["Const"]["Deduplicated"]))
    require(widths == [8, 8], "unexpected chunk widths")
    ops = []
    for stmt in inner:
        if stmt["id"] in CALLS:
            op, inputs = CALLS[stmt["id"]]
            require(stmt["kind"]["Call"]["call"]["args"] == [move(*arg) for arg in inputs],
                    "changed data flow in loop")
            ops.append("." + op)
    return (
        "-- Generated from the frozen AVX xor_assign LLBC by project.py.\n"
        "import BulksketchBridge.AvxXorLlbcRuntime\n\n"
        "namespace BulksketchBridge.AvxXorLlbc\n\n"
        "def program : Program :=\n"
        f"  ⟨{widths[0]}, {widths[1]}, [{', '.join(ops)}]⟩\n\n"
        "end BulksketchBridge.AvxXorLlbc\n"
    )


def check(root=ROOT):
    receipt = json.loads((root / EXTRACTION / "receipt.json").read_text())
    expected = {
        "frozen_source": "0a5bda53f6b07fcae8acd870e2d0c4a246d207e6",
        "source_checkout": "6f4d5089c093d8f8087b89520b45e534a42a5813",
        "target": "x86_64-apple-darwin",
        "rust_toolchain": "nightly-2026-09-17",
        "charon": "7b462d9159db2ed3015162352183906a30bfafc6",
        "aeneas": "ab34bd28458a08c150b7cbf1873e59af74588138",
        "checks": ["-checks", "-sequential"],
        "root": "bulksketch::backend::x86_vpclmul512::xor_assign",
        "charon_exit": 0, "aeneas_exit": 0, "native_body_proof_credit": 0,
    }
    require(all(receipt[key] == value for key, value in expected.items()), "unexpected extraction receipt")
    require(set(receipt["artifacts"]) == {f"{EXTRACTION}/{file}" for file in FILES},
            "extraction artifact set changed")
    for path, digest in receipt["artifacts"].items():
        require(sha((root / path).read_bytes()) == digest, "changed extraction artifact " + path)
    raw = (root / EXTRACTION / "arithmetic.llbc").read_bytes()
    require(sha(raw) == LLBC_SHA, "frozen LLBC digest changed")
    projected = projection(json.loads(raw), (root.parent.parent / SOURCE).read_text())
    require((root / GENERATED).read_text() == projected, "stateful AVX xor_assign projection differs")
    return {"compiled_projection": GENERATED, "projection_sha256": sha(projected.encode()),
            "llbc_sha256": LLBC_SHA, "source_sha256": SOURCE_SHA, "programs": {
                "src/backend/x86_vpclmul512.rs:364:function:bulksketch::backend::x86_vpclmul512::xor_assign":
                    "BulksketchBridge.AvxXorLlbc.program"},
            "native_body_proof_credit": 0}


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
