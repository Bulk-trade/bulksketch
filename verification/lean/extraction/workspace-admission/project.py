#!/usr/bin/env python3
"""Symbolically project the original read-only workspace-admission LLBC."""
from collections import Counter
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/workspace-admission")
GENERATED = Path("bridge/BulksketchBridge/WorkspaceAdmissionGenerated.lean")
SOURCE = Path("src/decode/stages.rs")
SOURCE_COMMIT = "0a5bda53f6b07fcae8acd870e2d0c4a246d207e6"
SOURCE_SHA = "93825fcb5054e98e9af060a81da72d4770c29354d79822ccfc949cc55f6e9b23"
LLBC_SHA = "2839bcdd234dc0ba589b89dc4f98a72a20c3206ab2a3f43e3f589710fe02c947"
REGISTRY_SHA = "81a421c7ca4e1ba6d9c2da2ecbbdc4ec74083cf6c29ae06d8042911df7c307c8"
PROGRAMS = (11, 24, 25)
FIELDS = ("syndromes", "bm", "polynomials", "factors", "squareTable", "verification", "roots", "raw", "stack")
HEADER = """-- Generated from the frozen check_workspace LLBC by project.py.
import BulksketchBridge.WorkspaceAdmissionSpec
import Workmeter.Types

namespace BulksketchBridge.WorkspaceAdmission

/-- Successful normal paths of the original LLBC. Every other return is ScratchTooSmall. -/
def sourceAccepts (lengths : Lengths) (capacity budget : Nat) : Prop :=
"""


FOOTER = """

open Aeneas.Std

instance (lengths : Lengths) (capacity budget : Nat) : Decidable (sourceAccepts lengths capacity budget) := by
  unfold sourceAccepts
  infer_instance

/-- The original shared workspace is preserved on every decoded return path. -/
def runOriginal {Workspace : Type} (lengths : Workspace → Lengths) (workspace : Workspace)
    (capacity budget : Usize) : core.result.Result Unit bulksketch.types.DecodeError × Workspace :=
  (if sourceAccepts (lengths workspace) capacity.val budget.val then .Ok () else .Err .ScratchTooSmall,
    workspace)

end BulksketchBridge.WorkspaceAdmission
"""


def require(valid, message):
    if not valid:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def singleton(data):
    require(isinstance(data, dict) and len(data) == 1, "expected one LLBC constructor")
    return next(iter(data.items()))


def collect_constants(document):
    constants = {}

    def visit(node):
        if isinstance(node, list):
            for item in node:
                visit(item)
        elif isinstance(node, dict):
            if set(node) == {"Value"} and isinstance(node["Value"], list) and len(node["Value"]) == 2:
                index, value = node["Value"]
                if isinstance(value, list) and len(value) == 2:
                    require(index not in constants or constants[index] == value, "ambiguous constant table")
                    constants[index] = value
            for item in node.values():
                visit(item)

    visit(document)
    return constants


def number(value):
    require(value[0] in ("nat", "var", "len", "add", "mul", "div"), "expected usize value")
    return value


def render_number(value):
    tag, *args = number(value)
    if tag in ("nat", "var"):
        return str(args[0])
    if tag == "len":
        return "lengths." + FIELDS[args[0]]
    left, right = args
    op = {"add": "+", "mul": "*", "div": "/"}[tag]
    return f"({render_number(left)} {op} {render_number(right)})"


def render_condition(condition, polarity):
    tag, left, *right = condition
    if tag == "fits":
        return f"{render_number(left)} {'≤' if polarity else '>'} usizeMax"
    op = {"eq": ("=", "≠"), "lt": ("<", "≥")}[tag][not polarity]
    return f"{render_number(left)} {op} {render_number(right[0])}"


class Projector:
    def __init__(self, document):
        self.functions = document["translated"]["fun_decls"]
        self.constants = collect_constants(document)
        self.read_fields = set()
        self.call_ids = Counter()
        self.returns = Counter()

    def const(self, encoded):
        tag, data = singleton(encoded)
        if tag == "Value":
            index, value = data
            require(self.constants[index] == value, "constant table mismatch")
        else:
            require(tag == "Deduplicated", "unsupported constant encoding")
            value = self.constants[data]
        constructor, payload = singleton(value[0])
        if constructor == "Integer":
            scalar = payload["Unsigned"]
            require(scalar[0] == "Usize", "unsupported integer width")
            return ("nat", int(scalar[1]))
        if constructor == "Adt":
            require(payload == [None, []], "unsupported constant aggregate")
            return ("unit",)
        if constructor == "Bool":
            return ("literal", payload)
        require(constructor == "Discriminant" and payload[0]["id"] == 10,
                "unsupported discriminant constant")
        return ("variant", payload[1])

    @staticmethod
    def force(value, conditions):
        while value[0] == "choose" and value[1] in conditions:
            value = value[2] if conditions[value[1]] else value[3]
        return value

    def place(self, place, locals_, conditions):
        kind, data = singleton(place["kind"])
        if kind == "Local":
            require(data in locals_, "read of missing local")
            return self.force(locals_[data], conditions)
        require(kind == "Projection", "unsupported place")
        origin, path = data
        value = self.place(origin, locals_, conditions)
        if path == "Deref":
            require(value[0] == "ref", "invalid dereference")
            return self.force(value[1], conditions)
        if path == "PtrMetadata":
            require(value[0] == "ref" and value[1][0] == "slice", "non-slice pointer metadata")
            return ("len", value[1][1])
        field = path["Field"]
        if value[0] == "workspace":
            require(field[0] is None and 0 <= field[1] < len(FIELDS), "invalid workspace field")
            return ("ref", ("slice", field[1]))
        if value[0] == "tuple":
            require(field[0] is None and 0 <= field[1] < len(value) - 1, "tuple field mismatch")
            return value[field[1] + 1]
        require(value[0] == "control" and field == [value[1], 0], "inaccessible enum field")
        return value[2]

    def operand(self, operand, locals_, conditions):
        tag, data = singleton(operand)
        if tag == "Const":
            return self.const(data)
        require(tag in ("Move", "Copy"), "unsupported operand")
        value = self.place(data, locals_, conditions)
        if tag == "Move" and "Local" in data["kind"]:
            del locals_[data["kind"]["Local"]]
        return value

    def expression(self, expression, locals_, conditions):
        tag, data = singleton(expression)
        if tag == "Use":
            require(data[1] in ("Yes", "No"), "unsupported value copy flag")
            return self.operand(data[0], locals_, conditions)
        if tag == "Ref":
            require(data["kind"] == "Shared", "workspace projection creates a writable loan")
            value = self.place(data["place"], locals_, conditions)
            metadata = self.operand(data["ptr_metadata"], locals_, conditions)
            require(metadata == (("len", value[1]) if value[0] == "slice" else ("unit",)), "bad ref metadata")
            return ("ref", value)
        if tag == "BinaryOp":
            operation, left, right = data
            left = number(self.operand(left, locals_, conditions))
            right = number(self.operand(right, locals_, conditions))
            if operation == {"Div": "Panic"}:
                require(right[0] == "nat" and right[1] > 0, "division could panic")
                return ("div", left, right)
            require(operation in ("Lt", "Eq"), "unexpected binary operation")
            return ("predicate", operation.lower(), left, right)
        require(tag == "Aggregate", "unsupported assignment expression")
        adt, variant, field = data[0]["Adt"]
        require(field is None, "unexpected aggregate field")
        values = tuple(self.operand(operand, locals_, conditions) for operand in data[1])
        if adt["id"] == 0:
            require(variant is None and adt["builtin"] == "Tuple" and len(values) in (0, 2), "invalid tuple")
            return ("tuple", *values) if values else ("unit",)
        if adt["id"] in (8, 9):
            require(variant is None and not values, "closure captures changed")
            return ("closure", adt["id"])
        if adt["id"] == 7:
            require(variant == 4 and not values, "error variant is not ScratchTooSmall")
            return ("error",)
        require(adt["id"] == 6 and variant in (0, 1) and len(values) == 1, "unexpected aggregate result")
        return ("result", variant, values[0])

    def call(self, data, locals_, conditions):
        call = data["call"]
        require(call["safety"] == "Inherit", "unexpected call safety")
        fn = call["func"]["Regular"]["kind"]["Fun"]
        self.call_ids[fn] += 1
        args = [self.operand(arg, locals_, conditions) for arg in call["args"]]
        cleanup = [item["kind"] for item in data["on_unwind"]["statements"]]
        require(cleanup[-1:] == ["UnwindResume"] and all(
            isinstance(item, dict) and set(item) == {"StorageDead"} for item in cleanup[:-1]), "unsupported unwind action")
        if fn in (24, 25):
            require(len(args) == 2 and args[0] == ("ref", ("closure", fn - 16)) and args[1][0] == "tuple", "incorrect closure args")
            body = self.functions[fn]["body"]["Structured"]["body"]["statements"]
            result = self.run(body, {1: args[0], 2: args[1]}, conditions, closure=True)
            require(len(result) == 1 and result[0][0] == conditions, "unexpected closure control flow")
            return result[0][1]
        if fn in (28, 32):
            require(len(args) == 2, "incorrect checked arithmetic args")
            result = (("add" if fn == 28 else "mul"), *map(number, args))
            return ("choose", ("fits", result), ("some", result), ("none",))
        if fn == 29:
            require(len(args) == 2 and args[1] == ("error",), "wrong ok_or error")
            return self.map_choice(args[0], lambda val: ("result", 0, val[1]) if val[0] == "some" else ("result", 1, args[1]))
        if fn == 20:
            require(len(args) == 1, "incorrect Try::branch args")
            def branch(val):
                require(val[0] == "result" and val[1] in (0, 1), "invalid Result branch")
                return ("control", val[1], val[2] if val[1] == 0 else val)
            return self.map_choice(args[0], branch)
        if fn == 21:
            require(args == [("result", 1, ("error",))], "wrong Result residual")
            return args[0]
        require(fn == 22 and len(args) == 1 and args[0][0] == "ref" and args[0][1][0] == "slice", "unsupported call")
        field = args[0][1][1]
        self.read_fields.add(field)
        return ("len", field)

    @staticmethod
    def map_choice(value, function):
        if value[0] == "choose":
            return ("choose", value[1], function(value[2]), function(value[3]))
        return function(value)

    def run(self, statements, locals_, conditions, closure=False):
        for index, statement in enumerate(statements):
            kind = statement["kind"]
            if kind == "Return":
                value = self.force(locals_[0], conditions)
                if not closure:
                    require(value in (("result", 0, ("unit",)), ("result", 1, ("error",))), "unknown return outcome")
                    self.returns[value[1]] += 1
                return [(conditions, value)]
            tag, data = singleton(kind)
            if tag in ("StorageLive", "StorageDead"):
                locals_.pop(data, None)
                continue
            if tag == "Borrowck":
                require(set(data) == {"FakeRead"}, "unexpected borrow-check marker")
                self.place(data["FakeRead"], locals_, conditions)
                continue
            if tag in ("Assign", "Call"):
                if tag == "Assign":
                    target, expression = data
                    value = self.expression(expression, locals_, conditions)
                else:
                    target = data["dest"]
                    value = self.call(data, locals_, conditions)
                require(set(target["kind"]) == {"Local"} and target["kind"]["Local"] != 1,
                        "workspace or nonlocal write")
                locals_[target["kind"]["Local"]] = value
                continue
            require(tag == "Switch", "unsupported control-flow statement")
            selector, operand = singleton(data["data"]["scrutinee"])
            if selector == "Value":
                value = self.operand(operand, locals_, conditions)
                require(value[0] == "predicate", "unexpected Bool switch value")
                guard = value[1:]
                values = ((True, ("literal", True)), (False, ("literal", False)))
            else:
                require(selector == "Discriminant", "unsupported switch selector")
                value = self.place(operand, locals_, conditions)
                require(value[0] in ("choose", "control"), "unexpected discriminant input")
                guard = value[1] if value[0] == "choose" else None
                values = ((True, ("variant", value[2][1])), (False, ("variant", value[3][1]))) if guard else ((True, ("variant", value[1])),)
            branches = {self.const(constant): branch for constant, branch in data["data"]["branches"]}
            results = []
            for polarity, key in values:
                if guard in conditions and conditions[guard] != polarity:
                    continue
                branch = branches.get(key, data["data"]["fallback"])
                require(type(branch) is int and 0 <= branch < len(data["branches"]), "unreachable or invalid switch alternative")
                next_conditions = conditions | ({guard: polarity} if guard is not None else {})
                results += self.run(data["branches"][branch]["statements"] + statements[index + 1:],
                                    locals_.copy(), next_conditions, closure=closure)
            return results
        raise ValueError("control-flow path has no return")


def registry_digest(document):
    # All type declarations, callee signatures, arguments' local types, and
    # extraction metadata stay frozen. Only the three decoded statement trees
    # are omitted from this digest so controls can exercise their projection.
    registry = deepcopy(document)
    for identifier in PROGRAMS:
        registry["translated"]["fun_decls"][identifier]["body"]["Structured"]["body"]["statements"] = []
    return digest(json.dumps(registry, sort_keys=True, separators=(",", ":")).encode())


def project(document):
    translated = document["translated"]
    root = translated["fun_decls"][11]
    name = [{"Ident": [part, 0]} for part in "bulksketch::decode::stages::check_workspace".split("::")]
    require(document["has_errors"] is False and root["item_meta"]["name"] == name, "wrong original LLBC root")
    require(translated["options"]["start_from"] == ["bulksketch::decode::stages::check_workspace"]
            and translated["options"]["opaque"] == [], "wrong workspace selector")
    target = translated["target_information"]
    require(len(target) == 1 and target[0]["key"] == "x86_64-apple-darwin"
            and target[0]["value"]["target_pointer_size"] == 8, "unexpected workspace target")
    item_span = root["item_meta"]["span"]["Untagged"]["data"]
    source = translated["files"][item_span["file_id"]]
    require(item_span["beg"] == {"line": 454, "col": 0} and item_span["end"] == {"line": 487, "col": 1}
            and source["name"] == {"Local": str(SOURCE)}, "incorrect source span")
    require(digest(source["contents"].encode()) == SOURCE_SHA, "frozen Rust source differs")
    row = translated["type_decls"][5]
    require([field["name"] for field in row["kind"]["Struct"]] == [
        "syndromes", "bm", "polynomials", "factors", "square_table", "verification", "roots", "raw", "stack", "basis"],
        "workspace field layout differs")
    require(registry_digest(document) == REGISTRY_SHA, "workspace LLBC registry differs")
    interpreter = Projector(document)
    results = interpreter.run(root["body"]["Structured"]["body"]["statements"],
        {1: ("ref", ("workspace",)), 2: ("var", "capacity"), 3: ("var", "budget")}, {})
    require(interpreter.read_fields == set(range(len(FIELDS))), "workspace field reads changed")
    success = [conds for conds, value in results if value[1] == 0]
    require(success and interpreter.returns[1], "missing workspace acceptance or rejection")
    rendered = ["  (" + " ∧\n    ".join(render_condition(cond, polarity) for cond, polarity in path.items()) + ")"
                for path in success]
    lean = HEADER + " ∨\n".join(rendered) + FOOTER
    return lean, {"normal_success_paths": len(success), "normal_error_paths": interpreter.returns[1],
                  "read_only_fields": list(FIELDS), "original_call_ids": dict(interpreter.call_ids)}


def check(root=ROOT):
    path = root / DIRECTORY / "arithmetic.llbc"
    raw = path.read_bytes()
    require(digest(raw) == LLBC_SHA, "frozen workspace LLBC differs")
    require(digest((root.parents[1] / SOURCE).read_bytes()) == SOURCE_SHA, "frozen Rust workspace source differs")
    generated, stats = project(json.loads(raw))
    require(generated == (root / GENERATED).read_text(), "compiled projection differs")
    projection_sha = digest(generated.encode())
    return {
        **stats,
        "programs": {"src/decode/stages.rs:454:function:bulksketch::decode::stages::check_workspace":
                     "BulksketchBridge.WorkspaceAdmission.runOriginal"},
        "source_commit": SOURCE_COMMIT,
        "source_sha256": SOURCE_SHA,
        "llbc_sha256": LLBC_SHA,
        "llbc": str(DIRECTORY / "arithmetic.llbc"),
        "compiled_projection": str(GENERATED),
        "projection_file_sha256": projection_sha,
        "projection_sha256": projection_sha,
        "native_body_proof_credit": 0,
        "native_source_edited": False,
    }


if __name__ == "__main__":
    if sys.argv[1:] == ["--emit"]:
        document = json.loads((ROOT / DIRECTORY / "arithmetic.llbc").read_text())
        generated, stats = project(document)
        (ROOT / GENERATED).write_text(generated)
        print(json.dumps(stats, indent=2))
    else:
        require(sys.argv[1:] == [], "unexpected arguments")
        print(json.dumps(check(), indent=2))
