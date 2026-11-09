"""Verify the original affine multiple iterator cleanup shape."""
from hashlib import sha256
import json

CAPTURE = "5c052e41228ab5a9a3bfe259389d2e1d5333bf09a063608bde61b66a105145d6"
SELECTOR = "bulksketch::decode::affine::multiple"
OPAQUE = ["bulksketch::poly::dense::_::square_mod_into"]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def nodes(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from nodes(child)
    elif isinstance(value, list):
        for child in value:
            yield from nodes(child)


def load(contents):
    require(sha256(contents).hexdigest() == CAPTURE, "not the original affine multiple capture")
    return json.loads(contents)


def select(capture):
    name = [{"Ident": [part, 0]} for part in SELECTOR.split("::")]
    declarations = [decl for decl in capture["translated"]["fun_decls"]
                    if decl and decl["item_meta"]["name"] == name]
    require(len(declarations) == 1, "expected one original affine multiple declaration")
    return declarations[0]


def lifetime_shapes(capture):
    body = select(capture)["body"]["Structured"]
    outer, = [stmt["kind"]["Loop"] for stmt in body["body"]["statements"] if stmt["id"] == 3576]
    locals = {entry["index"]: entry["name"] for entry in body["locals"]["locals"]}
    require(tuple(locals[i] for i in (14, 22, 39, 44, 191, 225)) ==
            ("rows", "witnesses", "vector", "witness", "iter", "iter"),
            "unexpected affine multiple scratch/iterator locals")
    spans = {span_id: span for node in nodes(body) if isinstance(node.get("span"), dict)
             and "Value" in node["span"] for span_id, span in [node["span"]["Value"]]}
    checked = []
    for loop_id, first, last, death_ids in (
        (2782, 149, 154, [194, 192, 191, 187, 170, 166]),
        (3312, 155, 160, [228, 226, 225, 221, 204, 200]),
    ):
        loop_position, = [index for index, stmt in enumerate(outer["statements"]) if stmt["id"] == loop_id]
        loop = outer["statements"][loop_position]
        deaths = outer["statements"][loop_position + 1:loop_position + 1 + len(death_ids)]
        require([s["kind"] for s in deaths] == [{"StorageDead": local} for local in death_ids],
                "affine multiple iterator lifetime boundary differs")
        span = loop["span"]["Value"][1]["data"]
        require((span["beg"], span["end"]) == ({"line": first, "col": 8}, {"line": last, "col": 9}),
                "affine multiple loop span differs")
        death_span = spans[deaths[2]["span"]["Deduplicated"]]["data"]
        require((death_span["beg"], death_span["end"]) == ({"line": last, "col": 8}, {"line": last, "col": 9}),
                "affine multiple terminal Zip storage-death span differs")
        require(not any(stmt.get("kind") == "Return" or isinstance(stmt.get("kind"), dict) and
                        any(stmt["kind"].get(edge, 0) != 0 for edge in ("Break", "Continue"))
                        for stmt in nodes(loop["kind"]["Loop"])),
                "affine multiple Zip has an exit bypassing the inspected cleanup")
        checked.append(f"Loop {loop_id} exits through ordered storage deaths {death_ids}.")
    return "\n".join(checked) + "\n"


def wrong_lifetime(contents):
    capture = load(contents)
    body = select(capture)["body"]["Structured"]["body"]
    statement, = [node for node in nodes(body)
                  if set(node) == {"span", "id", "kind", "comments_before"} and node["id"] == 2787]
    require(statement["kind"] == {"StorageDead": 191}, "unexpected affine multiple control statement")
    statement["kind"] = {"StorageDead": 192}
    return json.dumps(capture, ensure_ascii=False, separators=(",", ":")).encode()
