"""Mutate typed LLBC before its raw artifact hash check."""
from copy import deepcopy
import json

import project

project.check()
doc = json.loads((project.ROOT / project.DIRECTORY / "arithmetic.llbc").read_text())
source = (project.ROOT.parent.parent / project.SOURCE).read_text()


def body(value):
    return value["translated"]["fun_decls"][11]["body"]["Structured"]["body"]["statements"]


def stmt(statements, ident):
    return next(item for item in statements if item["id"] == ident)["kind"]


def loop(value):
    return stmt(body(value), 358)["Loop"]["statements"]


def call(statements, ident):
    return stmt(statements, ident)["Call"]["call"]


def omit_store(value):
    loop(value)[:] = [entry for entry in loop(value) if entry["id"] != 323]


def wrong_break(value):
    stmt(loop(value), 90)["Switch"]["branches"][0]["statements"][0]["kind"] = {"Continue": 0}


def pointer_offset(value):
    operand = stmt(loop(value), 216)["Assign"][1]["BinaryOp"][2]
    operand["Copy"]["kind"]["Local"] = 15


def mismatch_test(value):
    stmt(body(value), 370)["Assign"][1]["Use"][0]["Copy"]["kind"]["Local"] = 21


def xor_instead_of_or(value):
    call(loop(value), 344)["func"]["Regular"]["kind"]["Fun"] = 36


def stride(value):
    call(body(value), 51)["args"][1]["Const"] = {"Value": [999, [
        {"Integer": {"Unsigned": ["Usize", "16"]}}, {"Deduplicated": 0}]]}


def copied_pointer(value):
    operand = call(loop(value), 255)["args"][1]
    operand["Copy"] = operand.pop("Move")


def unwind(value):
    stmt(loop(value), 323)["Call"]["on_unwind"]["statements"].pop()


def endian(value):
    value["translated"]["target_information"][0]["value"]["is_little_endian"] = False


for change in (omit_store, wrong_break, pointer_offset, mismatch_test, xor_instead_of_or,
               stride, copied_pointer, unwind, endian):
    changed = deepcopy(doc)
    change(changed)
    try:
        project.projection(changed, source)
    except ValueError:
        print(f"rejected {change.__name__}")
    else:
        raise SystemExit(f"accepted changed difference LLBC: {change.__name__}")
