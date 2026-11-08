"""Check the semantic and structural gate independently of the raw file digest."""
from copy import deepcopy
import json

import project

project.check()
document = json.loads((project.ROOT / project.EXTRACTION / "arithmetic.llbc").read_text())
source = (project.ROOT.parent.parent / project.SOURCE).read_text()
expected = (project.ROOT / project.GENERATED).read_text()


def statement(doc, index):
    outer, inner = project.blocks(doc)
    return next(stmt for stmt in outer + inner if stmt["id"] == index)


def call(doc, index):
    return statement(doc, index)["kind"]["Call"]["call"]


def replace(doc, index, kind):
    statement(doc, index)["kind"] = kind


def remove_store(doc):
    _, inner = project.blocks(doc)
    inner.remove(statement(doc, 103))


def change_chunk_width(doc):
    call(doc, 14)["args"][1] = {"Const": {"Deduplicated": 7}}


def swap_loads(doc):
    call(doc, 78)["args"], call(doc, 88)["args"] = call(doc, 88)["args"], call(doc, 78)["args"]


def copy_destination(doc):
    operand = call(doc, 103)["args"][0]
    operand["Copy"] = operand.pop("Move")


def change_xor(doc):
    call(doc, 95)["func"]["Regular"]["kind"]["Fun"] = 25


def change_break(doc):
    branch = statement(doc, 61)["kind"]["Switch"]["branches"][0]
    branch["statements"][0]["kind"] = {"Continue": 0}


controls = {
    "chunk width": change_chunk_width,
    "load data flow": swap_loads,
    "destination copy": copy_destination,
    "xor callee": change_xor,
    "omitted store": remove_store,
    "break edge": change_break,
    "continue edge": lambda doc: replace(doc, 114, {"Break": 0}),
    "return": lambda doc: replace(doc, 126, "UnwindResume"),
}
for name, mutate in controls.items():
    variant = deepcopy(document)
    mutate(variant)
    try:
        if project.projection(variant, source) == expected:
            raise SystemExit("accepted altered LLBC: " + name)
    except ValueError:
        pass
    print("rejected " + name)
