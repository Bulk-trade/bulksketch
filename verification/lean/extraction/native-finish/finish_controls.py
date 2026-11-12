#!/usr/bin/env python3
"""Replay the checked finish boundary and its fail-closed controls."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess

CAPTURE = "828fe62e379ff1dc2b86aae2869ab1afcefe5a7b1b803737cc93cc7240effeb1"
FLAG = "BULKSKETCH_FINISH_BOUNDARY"
FLAGS = ["-backend", "lean", "-sequential", "-no-progress-bar", "-print-error-emitters", "-split-files"]
FILES = ("Funs.lean", "Types.lean", "FunsExternal_Template.lean")


def walk(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def select(crate):
    function, = [fn for fn in crate["translated"]["fun_decls"] if fn
                 and fn["item_meta"]["name"][-1].get("Ident") == ["finish", 0]]
    return function


def mutation(data, name):
    if sha256(data).hexdigest() != CAPTURE:
        raise ValueError("expected original finish capture")
    capture = json.loads(data)
    function = select(capture)
    if name == "wrong-site":
        span = function["item_meta"]["span"]["Untagged"]["data"]
        if span["beg"] != {"line": 442, "col": 4}:
            raise ValueError("unexpected original finish span")
        span["beg"]["col"] = 5
    elif name == "wrong-residual":
        residual, = [node["kind"]["Call"]["call"]["args"][0]["Move"]["kind"] for node in walk(function["body"])
                     if set(node) == {"span", "id", "kind", "comments_before"} and node["id"] == 77]
        if residual != {"Local": 17}:
            raise ValueError("unexpected original finish residual local")
        residual["Local"] = 16
    else:
        raise ValueError("unknown finish control")
    return json.dumps(capture, ensure_ascii=False, separators=(",", ":")).encode()


def run(stock, patched, capture, expected, compatibility, destination):
    destination.mkdir(parents=True, exist_ok=False)
    wrong_site = destination / "wrong-site.llbc"
    wrong_residual = destination / "wrong-residual.llbc"
    data = capture.read_bytes()
    for path, name in ((wrong_site, "wrong-site"), (wrong_residual, "wrong-residual")):
        path.write_bytes(mutation(data, name))
    cases = (
        ("stock", stock, capture, False, True, False, None),
        ("flag-off", patched, capture, False, True, False, None),
        ("unchecked", patched, capture, True, False, False, None),
        ("checked", patched, capture, True, True, False, expected),
        ("strict-joins", patched, capture, True, True, True, expected),
        ("wrong-site", patched, wrong_site, True, True, False, None),
        ("wrong-residual", patched, wrong_residual, True, True, False, None),
        ("run-next", patched, compatibility / "arithmetic.llbc", True, True, False, compatibility / "Arithmetic"),
    )

    def one(case):
        label, tool, llbc, enabled, checked, strict, reference = case
        output = destination / label
        output.mkdir()
        command = [str(tool), *FLAGS, *(["-checks"] if checked else []), *(["-strict-joins"] if strict else []),
                   "-dest", str(output), str(llbc)]
        env = {key: value for key, value in os.environ.items() if key != FLAG}
        environment = {FLAG: "1"} if enabled else {}
        with (output / "run.log").open("wb") as log:
            proc = subprocess.run(command, env=env | environment, stdout=log, stderr=subprocess.STDOUT)
        files = {}
        if reference is None:
            log = (output / "run.log").read_text()
            if label == "wrong-residual":
                diagnostic = "Unexpected original RowExecution::finish return boundary"
            else:
                diagnostic = "Found a case of unsupported nested borrows"
            if proc.returncode != 1 or diagnostic not in log:
                raise ValueError("rejection differs: " + label)
        else:
            files = {name: digest(output / name) for name in FILES}
            if proc.returncode or files != {name: digest(reference / name) for name in FILES}:
                raise ValueError("emitted bytes differ: " + label)
        return label, {"command": command, "environment": environment, "exit_code": proc.returncode,
                       "binary_sha256": digest(tool), "input_sha256": digest(llbc),
                       "log_sha256": digest(output / "run.log"), "outputs": files}

    with ThreadPoolExecutor(max_workers=2) as pool:
        return dict(pool.map(one, cases))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for option in ("stock", "patched", "capture", "expected", "compatibility", "destination"):
        parser.add_argument("--" + option, type=Path, required=True)
    args = parser.parse_args()
    result = run(**vars(args))
    (args.destination / "receipt.json").write_text(json.dumps(result, indent=2) + "\n")
    for label, row in result.items():
        print(label, row["exit_code"])
