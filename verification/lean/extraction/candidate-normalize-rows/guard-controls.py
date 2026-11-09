"""Checked row-local capture and negative source/owner controls."""
from concurrent.futures import ThreadPoolExecutor
from copy import deepcopy
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import subprocess
import sys

base = Path(__file__).resolve().parent
packaged = (base / "arithmetic.llbc").is_file()
original = base / "arithmetic.llbc" if packaged else base.parent / "arithmetic.llbc"
tooling = Path("/Users/junbug/bulk/bulksketch-proofs/tooling")
stock = tooling / "aeneas/src/_build/default/main.exe"
variant = Path(sys.argv[1])
out = base / "controls"
out.mkdir(exist_ok=True)
digest = sha256(original.read_bytes()).hexdigest()
if digest != "18f2316981699128ed715212a783610b02d2a0c7e821f111e63a94df105216fb":
    raise ValueError("wrong original row-local capture")
data = json.loads(original.read_bytes())
switch = "AENEAS_CHECKED_CANDIDATE_NORMALIZE_ROWS"


def nodes(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from nodes(child)
    elif isinstance(value, list):
        for child in value:
            yield from nodes(child)


def statement(body, identifier):
    matches = [node for node in nodes(body) if node.keys() ==
               {"id", "kind", "span", "comments_before"} and node["id"] == identifier]
    if len(matches) != 1:
        raise ValueError(f"wrong LLBC statement {identifier}")
    return matches[0]


def mutation(label, output):
    altered = deepcopy(data)
    function = altered["translated"]["fun_decls"][11]
    if function["item_meta"]["name"][-1]["Ident"][0] != "normalize_rows":
        raise ValueError("wrong function")
    body = function["body"]["Structured"]["body"]
    if label == "wrong-name":
        function["item_meta"]["name"][-1]["Ident"][0] = "normalize_rows_negative"
    elif label == "wrong-span":
        function["item_meta"]["span"]["Untagged"]["data"]["beg"]["col"] += 1
    elif label == "wrong-row-type":
        td = altered["translated"]["type_decls"][5]
        if td["item_meta"]["name"][-1]["Ident"][0] != "DecodeRow":
            raise ValueError("wrong row type")
        td["item_meta"]["name"][-1]["Ident"][0] = "DecodeRowNegative"
    elif label == "wrong-cleanup":
        st = statement(body, 827)
        if st["kind"] != {"StorageDead": 35}:
            raise ValueError("wrong row cleanup")
        st["kind"] = {"StorageDead": 34}
    elif label == "idle-iterator-use":
        iterator_place = deepcopy(statement(body, 325)["kind"]["Assign"][0])
        if iterator_place["kind"] != {"Local": 30}:
            raise ValueError("wrong iterator binding")
        loop = statement(body, 801)
        template = deepcopy(loop["kind"]["Loop"]["statements"][0])
        template["id"] = 10000000
        template["kind"] = {"PlaceMention": iterator_place}
        loop["kind"]["Loop"]["statements"].insert(0, template)
    else:
        raise ValueError(label)
    output.write_text(json.dumps(altered, separators=(",", ":")) + "\n")
    return output


def run(label, binary, capture, enabled=True, checked=True):
    folder = out / label
    folder.mkdir(exist_ok=True)
    if label.startswith("wrong-") or label == "idle-iterator-use":
        capture = mutation(label, folder / "arithmetic.llbc")
    env = os.environ.copy()
    env.pop(switch, None)
    if enabled:
        env[switch] = "1"
    cmd = [str(binary), "-backend", "lean", *(["-checks"] if checked else []),
           "-sequential", "-no-progress-bar", "-print-error-emitters", "-split-files",
           "-dest", str(folder / "Arithmetic"), str(capture)]
    log_path = folder / "aeneas.log"
    with log_path.open("w") as log:
        code = subprocess.run(cmd, env=env, stdout=log, stderr=log, check=False).returncode
    text = re.sub(r"\x1b\[[0-9;]*m", "", log_path.read_text())
    positive = label in ("checked", "shared-stock", "shared-variant", "row-stock", "row-variant")
    if positive:
        if code != 0 or "Error]" in text:
            raise ValueError(f"positive {label} failed {code}")
    else:
        if code != 1 or "Could not translate the body of function" not in text:
            raise ValueError(f"negative {label} lost the original failure {code}")
        if label in ("stock", "off", "wrong-name", "wrong-span", "wrong-row-type") and "Invariants.ml, line 914" not in text:
            raise ValueError(f"negative {label} failed at a different source boundary")
    outputs = {f.name: sha256(f.read_bytes()).hexdigest() for f in (folder / "Arithmetic").glob("*.lean")}
    return label, {"status": code, "command": cmd, "enabled": enabled, "checked": checked,
                   "input_sha256": sha256(capture.read_bytes()).hexdigest(),
                   "log_sha256": sha256(log_path.read_bytes()).hexdigest(),
                   "outputs": outputs}


shared = (base.parent / "candidate-normalize/arithmetic.llbc" if packaged
          else base.parent.parent / "normalize/arithmetic.llbc")
row = (base.parent / "candidate-row/arithmetic.llbc" if packaged
       else base.parent.parent / "row/arithmetic.llbc")
args = [
    ("stock", stock, original, False, True), ("off", variant, original, False, True),
    ("unchecked", variant, original, True, False), ("checked", variant, original, True, True),
    *((label, variant, original, True, True) for label in
      ("wrong-name", "wrong-span", "wrong-row-type", "wrong-cleanup", "idle-iterator-use")),
    ("shared-stock", stock, shared, False, True), ("shared-variant", variant, shared, True, True),
    ("row-stock", stock, row, False, True), ("row-variant", variant, row, True, True),
]
with ThreadPoolExecutor(max_workers=2) as pool:
    checks = dict(pool.map(lambda x: run(*x), args))
for name in ("shared", "row"):
    if checks[f"{name}-stock"]["outputs"] != checks[f"{name}-variant"]["outputs"]:
        raise ValueError(f"unrelated {name} artifacts differ")
(out / "receipt.json").write_text(json.dumps({"original_sha256": digest,
    "variant_sha256": sha256(variant.read_bytes()).hexdigest(), "checks": checks}, indent=2) + "\n")
print("Checked original and negative scope controls passed. Shared normalization and row accessor artifacts match stock.")
