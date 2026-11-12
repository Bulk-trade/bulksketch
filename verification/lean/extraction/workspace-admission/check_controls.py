#!/usr/bin/env python3
"""Exercise statement projection independently of the outer raw-file hash."""
from copy import deepcopy
import json

from project import DIRECTORY, ROOT, check, project


def nodes(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from nodes(child)
    elif isinstance(value, list):
        for child in value:
            yield from nodes(child)


def statements(document, identifier=11):
    return document["translated"]["fun_decls"][identifier]["body"]["Structured"]["body"]["statements"]


def find(root, tag, predicate=lambda _: True):
    return next(node[tag] for node in nodes(root) if tag in node and predicate(node[tag]))


def change_borrow(document):
    find(statements(document), "Ref")["kind"] = "Mut"


def change_comparison(document):
    find(statements(document), "BinaryOp", lambda op: op[0] == "Lt")[0] = "Eq"


def change_checked_arithmetic(document):
    call = find(statements(document, 24), "Call", lambda call: call["call"]["func"]["Regular"]["kind"] == {"Fun": 28})
    call["call"]["func"]["Regular"]["kind"]["Fun"] = 32


def change_error(document):
    error = find(statements(document, 24), "Aggregate", lambda data: data[0]["Adt"][0]["id"] == 7)
    error[0]["Adt"][1] = 3


def change_branch(document):
    switch = find(statements(document), "Switch", lambda switch: "Value" in switch["data"]["scrutinee"])
    switch["data"]["branches"][0][1], switch["data"]["fallback"] = (
        switch["data"]["fallback"], switch["data"]["branches"][0][1])


def change_metadata(document):
    borrow = find(statements(document), "Ref", lambda ref: "Copy" in ref["ptr_metadata"])
    pointer = borrow["ptr_metadata"]["Copy"]["kind"]["Projection"][0]
    pointer["kind"]["Projection"][1]["Field"][1] = 1


def change_workspace_write(document):
    find(statements(document), "Assign")[0]["kind"]["Local"] = 1


def change_unwind(document):
    cleanup = find(statements(document), "Call")["on_unwind"]["statements"]
    cleanup[-1]["kind"] = "Return"


def change_target(document):
    document["translated"]["target_information"][0]["value"]["target_pointer_size"] = 4


def main():
    original = json.loads((ROOT / DIRECTORY / "arithmetic.llbc").read_text())
    generated, expected = project(original)
    checked = check()
    if checked["normal_success_paths"] != 2 or checked["normal_error_paths"] != 34 or expected != {
            key: checked[key] for key in expected}:
        raise RuntimeError("unexpected positive control")
    print("PASS original workspace LLBC")
    controls = {
        "mutable workspace borrow": change_borrow,
        "changed length comparison": change_comparison,
        "changed checked arithmetic": change_checked_arithmetic,
        "wrong error variant": change_error,
        "reversed budget branch": change_branch,
        "mismatched slice metadata": change_metadata,
        "write to workspace input": change_workspace_write,
        "changed unwind terminal": change_unwind,
        "changed target width": change_target,
    }
    for name, change in controls.items():
        altered = deepcopy(original)
        change(altered)
        try:
            projected, _ = project(altered)
        except ValueError as error:
            print(f"diagnostic {name}: {error}")
        else:
            if projected == generated:
                raise RuntimeError(f"mutation retained the compiled projection: {name}")
            print(f"diagnostic {name}: compiled projection changed")
        print(f"rejected {name}")


if __name__ == "__main__":
    main()
