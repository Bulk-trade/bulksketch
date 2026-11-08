#!/usr/bin/env python3
"""Decode the two exact masked-memory bodies into the scoped LLBC interpreter."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
GENERATED = "bridge/BulksketchBridge/X86MaskedMemoryLlbcGenerated.lean"
SOURCE = "src/backend/x86_vpclmul512.rs"
EXTRACTION = "extraction/masked-memory"
SOURCE_COMMIT = "0a5bda53f6b07fcae8acd870e2d0c4a246d207e6"
SOURCE_SHA = "7a9c29dff254508671aa4122b20644b21a9cfb40f86ba5eaadce02bf680475d4"
LLBC_SHA = "986307e55be3936bb3d50bee8227e663f12a91abb7897e424fb37844697f6275"
# Bind the registry of local and callee declarations, resolved type definitions,
# compile options and source metadata. Normal-path instructions are decoded below.
REGISTRY_SHA = "711c41dfaed027d4ff60a82f9956bf6d8f15fe32ccc68e6e5762c65a1a60fb18"
LOCAL_TYPES = {
    11: [25, 26, 6, 0, 27, 28, 30, 31],
    12: [33, 34, 25, 35, 36, 37, 6, 0, 38, 25],
}
# In the bound declaration registry, each callee id denotes the exact original
# function (slice impls, pointer impls, local mask or x86 intrinsic).
# Entries give opcode, result type, instantiated argument types, generic types
# and an optional pointer mutability flag.
CALLS = {
    21: ("len", 0, ((27, 38),), (24,), None),
    22: ("mask", 6, ((0,),), (), None),
    23: ("asPtr", 30, ((31,),), (24,), False),
    24: ("cast", 28, ((30,),), (24, 29), False),
    25: ("load", 25, ((6,), (28,)), (), None),
    26: ("asPtr", 36, ((37,),), (24,), True),
    27: ("cast", 35, ((36,),), (24, 29), True),
    28: ("store", 33, ((35,), (6,), (25,)), (), None),
}
HEADER = """-- Generated from the frozen masked-memory LLBC by project_stateful.py.
import BulksketchBridge.X86MaskedMemoryLlbcRuntime

namespace BulksketchBridge.X86MaskedMemory.Llbc
"""


def require(valid, message):
    if not valid:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def place(slot, ty):
    return {"kind": {"Local": slot}, "ty": {"Deduplicated": ty}}


def local(value, types):
    slot = value.get("kind", {}).get("Local")
    require(type(slot) is int and 0 <= slot < len(types), "expected an in-range direct local")
    require(value == place(slot, types[slot]), "local place/type mismatch")
    return slot


def decode(stmt, root, regions):
    types = LOCAL_TYPES[root]
    kind = stmt["kind"]
    if kind == "Return":
        return "ret"
    require(isinstance(kind, dict) and len(kind) == 1, "unsupported statement")
    tag, data = next(iter(kind.items()))
    if tag in ("StorageLive", "StorageDead"):
        require(type(data) is int and 0 <= data < len(types), "invalid storage operation")
        return f"{'live' if tag == 'StorageLive' else 'dead'} {data}"
    if tag == "Assign":
        dest, rhs = data
        dst = local(dest, types)
        if "Ref" in rhs:
            ref = rhs["Ref"]
            writable = ref["kind"] == "TwoPhaseMut"
            require(ref["kind"] == ("TwoPhaseMut" if writable else "Shared"),
                    "unsupported slice borrow kind")
            require(types[dst] in ((37,) if writable else (27, 31, 38))
                    and (not writable or root == 12), "incorrect borrow type")
            origin = place(1, types[1])
            require(rhs == {"Ref": {
                "kind": ref["kind"],
                "place": {"kind": {"Projection": [origin, "Deref"]}, "ty": {"Deduplicated": 23}},
                "ptr_metadata": {"Copy": {
                    "kind": {"Projection": [origin, "PtrMetadata"]}, "ty": {"Deduplicated": 0}}},
            }}, "incorrect borrow place or slice metadata operand")
            return f"reborrow {dst} 1 {str(writable).lower()}"
        if rhs == {"Use": [{"Copy": place(2, 25)}, "Yes"]}:
            require(root == 12 and types[dst] == 25, "incorrect vector copy type")
            return f"copyRegister {dst} 2"
        empty = {"regions": [], "types": [], "const_generics": [], "trait_refs": []}
        require(root == 12 and dst == 0 and rhs == {"Aggregate": [
            {"Adt": [{"id": 0, "generics": empty, "builtin": "Tuple"}, None, None]}, []]},
            "unsupported assignment")
        return "initUnit 0"
    require(tag == "Call", "unsupported LLBC statement kind")
    require(set(data) == {"call", "dest", "on_unwind"}, "unsupported LLBC call")
    call = data["call"]
    regular = call["func"].get("Regular", {})
    fn = regular.get("kind", {}).get("Fun")
    require(fn in CALLS, "unrecognized callee")
    opcode, output, inputs, generic_types, writable = CALLS[fn]
    generic_regions = regular["generics"]["regions"]
    require(len(generic_regions) == (1 if fn in (21, 23, 26) else 0) and all(
        set(region) == {"Body"} and type(region["Body"]) is int and 0 < region["Body"] <= regions
        for region in generic_regions), "invalid call region")
    expected_fn = {"Regular": {"kind": {"Fun": fn}, "generics": {
        "regions": generic_regions, "types": [{"Deduplicated": ty} for ty in generic_types],
        "const_generics": [], "trait_refs": []}}}
    require(set(call) == {"func", "args", "safety"} and call["func"] == expected_fn
            and call["safety"] == "Inherit", "incorrect call target/generics/safety")
    dst = local(data["dest"], types)
    require(types[dst] == output and len(call["args"]) == len(inputs), "call result type or arity")
    args = []
    for operand, accepted in zip(call["args"], inputs):
        require(set(operand) == {"Move"}, "calls must preserve original Move operands")
        slot = local(operand["Move"], types)
        require(types[slot] in accepted, "call argument type mismatch")
        args.append(slot)
    cleanup = [entry["kind"] for entry in data["on_unwind"]["statements"]]
    require(cleanup == ([{"StorageDead": 1}] if root == 11 else
                        [{"StorageDead": 2}, {"StorageDead": 1}]) + ["UnwindResume"],
            "changed unwind cleanup")
    suffix = "" if writable is None else f" {str(writable).lower()}"
    return f"{opcode} {' '.join(map(str, [dst, *args]))}{suffix}"


PROGRAMS = ((11, "load", 195), (12, "store", 202))


def projection(document, source):
    translated = document["translated"]
    require(document["has_errors"] is False and translated["crate_name"] == "bulksketch",
            "unexpected or incomplete LLBC")
    targets = translated["target_information"]
    require(len(targets) == 1 and targets[0]["key"] == "x86_64-apple-darwin"
            and targets[0]["value"]["is_little_endian"] is True
            and targets[0]["value"]["target_pointer_size"] == 8, "unexpected LLBC target")
    require(digest(source.encode()) == SOURCE_SHA
            and translated["files"][6]["name"] == {"Local": SOURCE}
            and translated["files"][6]["contents"] == source, "native source pin mismatch")
    registry = deepcopy(document)
    for root in LOCAL_TYPES:
        registry["translated"]["fun_decls"][root]["body"]["Structured"]["body"]["statements"] = []
    encoded = json.dumps(registry, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()
    require(digest(encoded) == REGISTRY_SHA, "frozen LLBC declarations or metadata changed")
    definitions = []
    for root, name, _ in PROGRAMS:
        decl = translated["fun_decls"][root]
        span = decl["item_meta"]["span"]["Untagged"]["data"]
        lines = source.splitlines(keepends=True)
        begin, end = span["beg"], span["end"]
        rust = (lines[begin["line"] - 1][begin["col"]:] + "".join(lines[begin["line"]:end["line"] - 1])
                + lines[end["line"] - 1][:end["col"]])
        require(span["file_id"] == 6 and rust == decl["item_meta"]["source_text"],
                "LLBC source span mismatch")
        block = decl["body"]["Structured"]
        stmts = block["body"]["statements"]
        ids = [stmt["id"] for stmt in stmts]
        require(ids == sorted(set(ids)), "unexpected statement order")
        ops = [decode(stmt, root, block["bound_body_regions"]) for stmt in stmts]
        require(ops[-1:] == ["ret"] and "ret" not in ops[:-1], "missing or premature return")
        lines = [f"  .{op}{',' if index + 1 < len(ops) else ']'} -- LLBC {ids[index]}"
                 for index, op in enumerate(ops)]
        definitions.append(f"\ndef {name}Program : List Op := [\n" + "\n".join(lines) + "\n")
    return HEADER + "".join(definitions) + "\nend BulksketchBridge.X86MaskedMemory.Llbc\n"


def check(root=ROOT):
    receipt = json.loads((root / EXTRACTION / "receipt.json").read_text())
    require(receipt["frozen_source"] == SOURCE_COMMIT
            and receipt["source_checkout"] == "6d6c82732855633305285910d4969df40410741e"
            and receipt["charon"] == "7b462d9159db2ed3015162352183906a30bfafc6"
            and receipt["aeneas"] == "ab34bd28458a08c150b7cbf1873e59af74588138"
            and receipt["checks"] == ["-checks", "-sequential"]
            and receipt["native_body_proof_credit"] == 0, "unexpected extraction receipt")
    raw = (root / EXTRACTION / "arithmetic.llbc").read_bytes()
    require(digest(raw) == LLBC_SHA, "frozen LLBC file changed")
    projected = projection(json.loads(raw), (root.parent.parent / SOURCE).read_text())
    require((root / GENERATED).read_text() == projected, "stateful LLBC projection differs")
    programs = {
        f"{SOURCE}:{line}:function:bulksketch::backend::x86_vpclmul512::{name}":
        f"BulksketchBridge.X86MaskedMemory.Llbc.{name}Program"
        for _, name, line in PROGRAMS
    }
    return {"compiled_projection": GENERATED, "projection_sha256": digest(projected.encode()),
            "llbc_sha256": LLBC_SHA, "source_sha256": SOURCE_SHA, "programs": programs,
            "native_body_proof_credit": 0}


if __name__ == "__main__":
    require(len(sys.argv) == 1, "the projector check takes no arguments")
    print(json.dumps(check(), indent=2))
