#!/usr/bin/env python3
"""Construct a negative control with the same U64 slice loan in the wrong field."""
import hashlib
import json

CAPTURE = "2b229999577f9864a20688af9bbaf205f039181095ac9f45a9d2b396297a723e"


def walk(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def load(data):
    if hashlib.sha256(data).hexdigest() != CAPTURE:
        raise ValueError("expected original exact deflate capture")
    return json.loads(data)


def select(llbc):
    stages = [fn for fn in llbc["translated"]["fun_decls"] if fn
              and fn["item_meta"]["name"][-1].get("Ident") == ["deflate", 0]]
    if len(stages) != 1 or not isinstance(stages[0]["body"], dict) or "Structured" not in stages[0]["body"]:
        raise ValueError("expected one original structured deflate body")
    return stages[0]


def wrong_owner(data):
    llbc = load(data)
    statement, = [node for node in walk(select(llbc)["body"])
                  if set(node) == {"span", "id", "kind", "comments_before"} and node["id"] == 271]
    fields = [node["Field"] for node in walk(statement) if set(node) == {"Field"}]
    if fields != [[None, 6], [None, 6]]:
        raise ValueError("expected both roots place projections")
    for field in fields:
        field[1] = 0
    return json.dumps(llbc, ensure_ascii=False, separators=(",", ":")).encode()
