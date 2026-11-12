#!/usr/bin/env python3
"""Reproduce checked translation and scope controls with pinned external tools."""
from argparse import ArgumentParser
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess

FLAG = "BULKSKETCH_DISPATCH_COMPLETED_RESULT"
FLAGS = ["-backend", "lean", "-sequential", "-no-progress-bar", "-print-error-emitters", "-split-files"]
SITES = {
    "wrong-site": ({"line": 175, "col": 8}, {"line": 186, "col": 5}),
    "wrong-assert": ({"line": 177, "col": 16}, {"line": 177, "col": 70}),
}
REJECT = {
    "stock": ("175:8-186:5", "interp/Invariants.ml, line 212"),
    "flag-off": ("175:8-186:5", "interp/Invariants.ml, line 212"),
    "unchecked": ("171:4-186:5", "interp/InterpBorrows.ml, line 1542"),
    "wrong-site": ("175:9-186:5", "interp/Invariants.ml, line 212"),
    "wrong-assert": ("177:17-177:70", "interp/Invariants.ml, line 212"),
    "wrong-workspace": ("175:8-186:5", "interp/Invariants.ml, line 212"),
}
CAPTURE = "967f971106c8c1e83170ff6d4179a4901986b2db72f110cd35d193dffed5edbe"


def walk(node):
    if isinstance(node, dict):
        yield node
        for child in node.values():
            yield from walk(child)
    elif isinstance(node, list):
        for child in node:
            yield from walk(child)


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def outputs(directory):
    return {file.name: digest(file) for file in sorted(directory.glob("*.lean"))}


def mutation(data, label):
    if sha256(data).hexdigest() != CAPTURE:
        raise ValueError("expected the original public result capture")
    capture = json.loads(data)
    crate = capture["translated"]
    if label == "wrong-workspace":
        decl, = [entry for entry in crate["type_decls"] if entry and
                 entry["item_meta"]["name"][-1].get("Ident") == ["RowWorkspace", 0]]
        decl["item_meta"]["name"][-1]["Ident"][0] = "OtherWorkspace"
    else:
        beg, end = SITES[label]
        matching = []
        for node in walk(crate):
            value = node.get("Value")
            if isinstance(value, list) and len(value) == 2 and isinstance(value[1], dict):
                span = value[1].get("data")
                if isinstance(span, dict) and span.get("beg") == beg and span.get("end") == end:
                    matching.append(span)
        if not matching:
            raise ValueError("missing original switch span")
        for span in matching:
            span["beg"]["col"] += 1
    return json.dumps(capture, ensure_ascii=False, separators=(",", ":")).encode()


def run(stock, patched, capture, compatibility, destination):
    destination.mkdir(parents=True)
    data = capture.read_bytes()
    if sha256(data).hexdigest() != CAPTURE:
        raise ValueError("expected the original public result capture")
    cases = []
    for label in (*SITES, "wrong-workspace"):
        fixture = destination / (label + ".llbc")
        fixture.write_bytes(mutation(data, label))
        cases.append((label, patched, fixture, True, True, False, None))
    expected = outputs(capture.parent / "Arithmetic")
    cases.extend((
        ("stock", stock, capture, False, True, False, None),
        ("flag-off", patched, capture, False, True, False, None),
        ("unchecked", patched, capture, True, False, False, None),
        ("checked", patched, capture, True, True, False, expected),
        ("replay", patched, capture, True, True, False, expected),
        ("strict", patched, capture, True, True, True, expected),
        ("compatibility", patched, compatibility / "arithmetic.llbc", True, True, False,
         outputs(compatibility / "Arithmetic")),
    ))

    def one(case):
        label, tool, source, enabled, checked, strict, reference = case
        output = destination / label
        output.mkdir()
        argv = [str(tool), *FLAGS, *(["-checks"] if checked else []),
                *(["-strict-joins"] if strict else []), "-dest", str(output), str(source)]
        env = {key: value for key, value in os.environ.items() if key != FLAG}
        if enabled:
            env[FLAG] = "1"
        with (output / "run.log").open("wb") as log:
            execution = subprocess.run(argv, env=env, stdout=log, stderr=subprocess.STDOUT)
        actual = outputs(output)
        if reference is None:
            span, compiler = REJECT[label]
            log = (output / "run.log").read_text()
            if execution.returncode != 1 or compiler not in log or (
                f"Source: 'src/sketch/dispatch.rs', lines {span}" not in log
            ):
                raise ValueError("rejection differs: " + label)
        elif execution.returncode or actual != reference:
            raise ValueError("checked output differs: " + label)
        return label, {"command": argv, "status": execution.returncode, "outputs": actual}

    with ThreadPoolExecutor(max_workers=2) as pool:
        return dict(pool.map(one, cases))


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    for option in ("stock", "patched", "capture", "compatibility", "destination"):
        parser.add_argument("--" + option, type=Path, required=True)
    args = parser.parse_args()
    result = run(**vars(args))
    (args.destination / "receipt.json").write_text(json.dumps(result, indent=2) + "\n")
    for label, row in result.items():
        print(label, row["status"])
