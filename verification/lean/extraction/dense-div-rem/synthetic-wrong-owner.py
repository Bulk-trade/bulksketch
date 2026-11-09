"""Create an intentionally changed LLBC control for the native Zip preflight."""
import json
from hashlib import sha256
from pathlib import Path
import sys

source, target = map(Path, sys.argv[1:])
frozen = source.read_bytes()
if sha256(frozen).hexdigest() != "1e565faa140b2f226dc3652de37ee8dcc0bfd5de2894b692e05a207d4c1d8b0c":
    raise ValueError("expected original frozen capture")
tree = json.loads(frozen)
crate = tree["translated"]
method = next(fun for fun in crate["fun_decls"] if fun and
              fun["item_meta"]["name"][-1].get("Ident") == ["div_rem_into", 0])
body = method["body"]["Structured"]


def walk(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


zip_input, = [node for node in walk(body["body"])
              if set(node) == {"span", "id", "kind", "comments_before"} and node["id"] == 641]
place = zip_input["kind"]["Assign"][1]["Use"][0]["Copy"]
if place["kind"] != {"Local": 1}:
    raise ValueError("expected raw initialization Zip input to be a")
place["kind"]["Local"] = 2
place["ty"] = body["locals"]["locals"][2]["ty"]
target.write_text(json.dumps(tree, ensure_ascii=False, separators=(",", ":")))
