#!/usr/bin/env python3
"""Replay original completed_result, rejection controls, and unrelated verification."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess

CAPTURE = "bfc4339f46f175a4e89f2afc38d88a90ed9506c306f71423293ef4a3f20f1673"
FLAG = "BULKSKETCH_COMPLETED_RESULT"
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


def mutation(data, name):
    if sha256(data).hexdigest() != CAPTURE:
        raise ValueError("expected the original completed_result capture")
    crate = json.loads(data)
    if name == "wrong-site":
        span, = [node["Value"][1]["data"] for node in walk(crate)
                 if isinstance(node.get("Value"), list) and len(node["Value"]) == 2
                 and node["Value"][0] == 30 and isinstance(node["Value"][1], dict)
                 and isinstance(node["Value"][1].get("data"), dict)
                 and node["Value"][1]["data"].get("beg") == {"line": 146, "col": 8}
                 and node["Value"][1]["data"].get("end") == {"line": 157, "col": 5}]
        span["beg"]["col"] = 9
    elif name == "wrong-workspace":
        decl, = [entry for entry in crate["translated"]["type_decls"] if entry
                 and entry["item_meta"]["name"][-1].get("Ident") == ["RowWorkspace", 0]]
        decl["item_meta"]["name"][-1]["Ident"][0] = "OtherWorkspace"
    else:
        raise ValueError("unknown completed_result control")
    return json.dumps(crate, ensure_ascii=False, separators=(",", ":")).encode()


def run(stock, patched, capture, expected, compatibility, destination):
    destination.mkdir(parents=True, exist_ok=False)
    wrong_site = destination / "wrong-site.llbc"
    wrong_workspace = destination / "wrong-workspace.llbc"
    data = capture.read_bytes()
    for path, name in ((wrong_site, "wrong-site"), (wrong_workspace, "wrong-workspace")):
        path.write_bytes(mutation(data, name))
    cases = (
        ("stock", stock, capture, False, True, None),
        ("flag-off", patched, capture, False, True, None),
        ("unchecked", patched, capture, True, False, None),
        ("checked", patched, capture, True, True, expected),
        ("wrong-site", patched, wrong_site, True, True, None),
        ("wrong-workspace", patched, wrong_workspace, True, True, None),
        ("execution-verify", patched, compatibility / "arithmetic.llbc", True, True, compatibility / "Arithmetic"),
    )

    def one(case):
        label, tool, llbc, enabled, checked, reference = case
        output = destination / label
        output.mkdir()
        command = [str(tool), *FLAGS, *(["-checks"] if checked else []), "-dest", str(output), str(llbc)]
        env = {key: value for key, value in os.environ.items() if key != FLAG}
        environment = {FLAG: "1"} if enabled else {}
        with (output / "run.log").open("wb") as log:
            proc = subprocess.run(command, env=env | environment, stdout=log, stderr=subprocess.STDOUT)
        files = {}
        if reference is None:
            log = (output / "run.log").read_text()
            expected_error = "Compiler source: interp/InterpBorrows.ml, line 1542" if label == "unchecked" else                 "Compiler source: interp/Invariants.ml, line 212"
            span = "142:4-157:5" if label == "unchecked" else "146:9-157:5" if label == "wrong-site" else "146:8-157:5"
            if (proc.returncode != 1 or expected_error not in log or
                "Could not translate the body" not in log or f"Source: 'src/decode/stages.rs', lines {span}" not in log):
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
