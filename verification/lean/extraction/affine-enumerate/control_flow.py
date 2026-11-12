"""Audit the frozen affine enumerator's normal control flow and generate guard controls."""
from copy import deepcopy
from hashlib import sha256
import json

SELECTOR = "bulksketch::decode::affine::enumerate"
CAPTURE = "6af0ef22080f0cd7ee6884689b8e14984b00e6afd203f5303bf255819c6e536a"
OUTER_CONTINUE = 1054
ERROR_EXITS = (1080, 1102)
SINK_CLEANUP = (111, 110, 109, 108, 106, 105, 101, 96, 92, 47, 46, 45, 43)
OUTER_CLEANUP = (42, 37)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def enumerate_body(capture):
    name = [{"Ident": [part, 0]} for part in SELECTOR.split("::")]
    matches = [decl for decl in capture["translated"]["fun_decls"]
               if decl and decl["item_meta"]["name"] == name]
    require(len(matches) == 1, "expected one original affine enumerator")
    return matches[0], matches[0]["body"]["Structured"]["body"]


def nodes(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from nodes(child)
    elif isinstance(value, list):
        for child in value:
            yield from nodes(child)


def statement_at(block, identifier):
    matches = [node for node in nodes(block)
               if set(node) == {"span", "id", "kind", "comments_before"} and node["id"] == identifier]
    require(len(matches) == 1, f"unexpected LLBC statement set at {identifier}")
    return matches[0]


def check_shape(body):
    outer = statement_at(body, 1158)["kind"]["Loop"]
    inner = statement_at(outer, 1138)
    epilogue = outer["statements"][outer["statements"].index(inner) + 1:]
    require([statement["kind"] for statement in epilogue] ==
            [{"StorageDead": index} for index in (*SINK_CLEANUP, *OUTER_CLEANUP)] + [{"Break": 0}],
            "unexpected original affine error epilogue")
    jumps = [(statement["id"], statement["kind"]) for statement in nodes(inner)
             if set(statement) == {"span", "id", "kind", "comments_before"}
             and statement["kind"] in ({"Continue": 1}, {"Break": 0})]
    require(jumps == [(OUTER_CONTINUE, {"Continue": 1}), *[(n, {"Break": 0}) for n in ERROR_EXITS]],
            "unexpected original affine inner-loop exit set")
    store_error = statement_at(inner, 1097)["kind"]["Assign"]
    store_result = statement_at(inner, 1098)["kind"]["Assign"]
    require(store_error[0]["kind"] == {"Local": 119}
            and store_error[1]["Aggregate"][1] == []
            and store_result[0]["kind"] == {"Local": 0}
            and len(store_result[1]["Aggregate"][1]) == 1
            and store_result[1]["Aggregate"][1][0]["Move"]["kind"] == {"Local": 119},
            "unexpected original affine unused return constructor")


def check_return_place(body):
    """Forget the return value on the original continue and check all normal exits."""
    seen_continue = set()

    def contains_return_place(value):
        if isinstance(value, dict):
            return value == {"Local": 0} or any(contains_return_place(v) for v in value.values())
        return isinstance(value, list) and any(contains_return_place(v) for v in value)

    def analyze_block(block, initial):
        outcomes = {("next", initial)}
        for statement in block["statements"]:
            following = set()
            for effect, assigned in outcomes:
                if effect == "next":
                    following.update(analyze_statement(statement, assigned))
                else:
                    following.add((effect, assigned))
            outcomes = following
        return outcomes

    def analyze_statement(statement, assigned):
        kind = statement["kind"]
        if kind == "Return":
            require(assigned, f"return {statement['id']} reachable without a fresh result assignment")
            return {("return", assigned)}
        if kind in ("UnwindResume", "UndefinedBehavior", "UnwindTerminate") or "Panic" in kind:
            return {("halt", assigned)}
        if isinstance(kind, dict) and "Assign" in kind:
            place, expression = kind["Assign"]
            require(not contains_return_place(expression), "explicit read of the return place")
            if place["kind"] == {"Local": 0}:
                return {("next", True)}
            require(not contains_return_place(place), "partial return-place write")
        elif isinstance(kind, dict) and "Loop" in kind:
            seen = set()
            work = {assigned}
            outcomes = set()
            while work:
                state = work.pop()
                if state in seen:
                    continue
                seen.add(state)
                for effect, state in analyze_block(kind["Loop"], state):
                    if effect in ("next", ("continue", 0)):
                        work.add(state)
                    elif effect == ("break", 0):
                        outcomes.add(("next", state))
                    elif isinstance(effect, tuple):
                        label, distance = effect
                        outcomes.add(((label, distance - 1), state))
                    else:
                        outcomes.add((effect, state))
            return outcomes
        elif isinstance(kind, dict) and "Switch" in kind:
            switch = kind["Switch"]
            require(not contains_return_place(switch["data"]), "branch reads the return place")
            return {outcome for branch in switch["branches"] for outcome in analyze_block(branch, assigned)}
        elif kind in ({"StorageLive": 0}, {"StorageDead": 0}):
            return {("next", False)}
        elif isinstance(kind, dict) and "Continue" in kind:
            if statement["id"] == OUTER_CONTINUE:
                require(kind == {"Continue": 1}, "unexpected original jump")
                seen_continue.add(statement["id"])
                assigned = False
            return {(("continue", kind["Continue"]), assigned)}
        elif isinstance(kind, dict) and "Break" in kind:
            return {(("break", kind["Break"]), assigned)}
        else:
            require(not contains_return_place(kind), "unrecognized operation refers to the return place")
        return {("next", assigned)}

    final = analyze_block(body, False)
    require(seen_continue == {OUTER_CONTINUE} and ("return", True) in final
            and all(effect in ("return", "halt") for effect, _ in final),
            "unexpected original affine normal exits")
    return "All reachable returns assign the original result after any visit to Continue 1 at statement 1054."


def altered_capture(capture, control):
    changed = deepcopy(capture)
    declaration, body = enumerate_body(changed)
    if control == "wrong-name":
        declaration["item_meta"]["name"][-1]["Ident"][0] = "scope_control"
    elif control == "wrong-span":
        span = declaration["item_meta"]["span"]["Untagged"]["data"]
        require(span["beg"] == {"line": 302, "col": 0}, "unexpected source span for control")
        span["beg"]["col"] = 1
    elif control == "wrong-cleanup":
        statement = statement_at(body, 1139)
        require(statement["kind"] == {"StorageDead": 111}, "unexpected cleanup control source")
        statement["kind"] = "Nop"
    elif control == "wrong-break":
        statement = statement_at(body, ERROR_EXITS[0])
        require(statement["kind"] == {"Break": 0}, "unexpected break control source")
        statement["id"] = 1 + max(node.get("id", 0) for node in nodes(body)
                                   if isinstance(node.get("id", 0), int))
    elif control == "wrong-constructor":
        constructor = statement_at(body, 1098)["kind"]["Assign"][1]
        require(constructor["Aggregate"][1][0]["Move"]["kind"] == {"Local": 119},
                "unexpected original constructor control source")
        constructor["Aggregate"][1][0]["Move"]["kind"]["Local"] = 115
    elif control == "missing-return-assignment":
        statement_at(body, 1098)["kind"] = "Nop"
    else:
        raise ValueError(f"unknown control {control}")
    return json.dumps(changed, ensure_ascii=False, separators=(",", ":")).encode()


def frozen_capture(contents):
    require(sha256(contents).hexdigest() == CAPTURE, "frozen affine enumeration capture differs")
    return json.loads(contents)
