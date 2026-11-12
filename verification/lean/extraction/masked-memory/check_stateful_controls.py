"""Focused LLBC negative controls, independent of the receipt's raw hash check."""
import copy
import json
import runpy

import project_stateful as projector

receipt = projector.check()
document = json.loads((projector.ROOT / projector.EXTRACTION / "arithmetic.llbc").read_text())
source = (projector.ROOT.parent.parent / projector.SOURCE).read_text()
expected = (projector.ROOT / projector.GENERATED).read_text()


def stmt(doc, statement):
    body = doc["translated"]["fun_decls"][12]["body"]["Structured"]["body"]
    return next(item for item in body["statements"] if item["id"] == statement)

def call(doc, statement):
    return stmt(doc, statement)["kind"]["Call"]["call"]

def drop(doc, statement):
    body = doc["translated"]["fun_decls"][12]["body"]["Structured"]["body"]
    body["statements"].remove(stmt(doc, statement))

def callee(doc):
    call(doc, 67)["func"]["Regular"]["kind"]["Fun"] = 25

def pointer_copy(doc):
    operand = call(doc, 67)["args"][0]
    operand["Copy"] = operand.pop("Move")

def pointer_projection(doc):
    ref = stmt(doc, 37)["kind"]["Assign"][1]["Ref"]
    ref["ptr_metadata"]["Copy"]["kind"]["Projection"][1] = "Deref"

def return_change(doc):
    stmt(doc, 73)["kind"] = "UnwindResume"

def byte_order(doc):
    doc["translated"]["target_information"][0]["value"]["is_little_endian"] = False

def cleanup_change(doc):
    stmt(doc, 67)["kind"]["Call"]["on_unwind"]["statements"].pop()

def local_type_change(doc):
    doc["translated"]["fun_decls"][12]["body"]["Structured"]["locals"]["locals"][3]["ty"] = {"Deduplicated": 28}

controls = {
    "callee": callee,
    "pointer copy": pointer_copy,
    "pointer metadata projection": pointer_projection,
    "drop mutable borrow": lambda doc: drop(doc, 37),
    "drop write": lambda doc: drop(doc, 67),
    "return": return_change,
    "target byte order": byte_order,
    "unwind cleanup": cleanup_change,
    "local type": local_type_change,
}
for name, change in controls.items():
    mutated = copy.deepcopy(document)
    change(mutated)
    try:
        if projector.projection(mutated, source) == expected:
            raise SystemExit(f"accepted altered LLBC: {name}")
    except ValueError:
        pass
    print(f"rejected {name}")

# Exercise the exact aggregate gate after the LLBC projection succeeds.
linkage = json.loads((projector.ROOT / "bridge/source-linkage.json").read_text())
entry = linkage["stateful_llbc_projection"]
verify = runpy.run_path(str(projector.ROOT / "scripts/verify_bridge.py"))
check_linkage = verify["check_stateful_linkage"]
check_linkage(entry, receipt, [])

swapped = copy.deepcopy(entry)
first, second = tuple(swapped["programs"])
swapped["programs"][first], swapped["programs"][second] = swapped["programs"][second], swapped["programs"][first]
for name, stateful, aeneas in (
    ("swapped source and program", swapped, []),
    ("false Aeneas projection credit", entry, [{"bridge_copy": entry["program_file"]}]),
):
    try:
        check_linkage(stateful, receipt, aeneas)
    except RuntimeError:
        print(f"rejected {name}")
    else:
        raise SystemExit(f"accepted altered LLBC association: {name}")
