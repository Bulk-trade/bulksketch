#!/usr/bin/env python3
"""Replay the checked original deflate capture and its scoped translator controls."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import subprocess

from wrong_roots_loan import wrong_owner

OUTPUTS = ("Types.lean", "Funs.lean", "FunsExternal_Template.lean")
FLAG = "BULKSKETCH_DEFLATE"
FLAGS = ["-backend", "lean", "-sequential", "-no-progress-bar", "-print-error-emitters", "-split-files"]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def replay(stock, patched, capture, expected, compatibility, destination):
    destination.mkdir(parents=True, exist_ok=False)
    wrong = destination / "wrong-roots-loan.llbc"
    wrong.write_bytes(wrong_owner(capture.read_bytes()))
    cases = (
        ("stock", stock, capture, False, True, None),
        ("flag-off", patched, capture, False, True, None),
        ("unchecked", patched, capture, True, False, None),
        ("checked", patched, capture, True, True, expected),
        ("wrong-roots-loan", patched, wrong, True, True, None),
        ("execution-verify", patched, compatibility / "arithmetic.llbc", True, True, compatibility / "Arithmetic"),
    )

    def run(case):
        name, executable, source, enabled, checked, reference = case
        output = destination / name
        output.mkdir()
        command = [str(executable), *FLAGS, *(["-checks"] if checked else []),
                   "-dest", str(output), str(source)]
        environment = {FLAG: "1"} if enabled else {}
        env = {key: value for key, value in os.environ.items() if key != FLAG}
        log = output / "run.log"
        with log.open("wb") as handle:
            result = subprocess.run(command, env=env | environment, stdout=handle, stderr=subprocess.STDOUT)
        outputs = {}
        if reference is None:
            diagnostic = log.read_text()
            if (result.returncode != 1 or "Could not translate the body" not in diagnostic
                or "Source: 'src/decode/stages.rs', lines 321:8-333:5" not in diagnostic
                or "Compiler source: interp/InterpMatchCtxs.ml, line 649" not in diagnostic):
                raise ValueError("deflate rejection differs: " + name)
        else:
            outputs = {file: digest(output / file) for file in OUTPUTS}
            if result.returncode or outputs != {file: digest(reference / file) for file in OUTPUTS}:
                raise ValueError("deflate checked replay differs: " + name)
        return name, {"command": command, "environment": environment, "exit_code": result.returncode,
                      "binary_sha256": digest(executable), "input_sha256": digest(source),
                      "log_sha256": digest(log), "outputs": outputs}

    with ThreadPoolExecutor(max_workers=2) as pool:
        return dict(pool.map(run, cases))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("stock", "patched", "capture", "expected", "compatibility", "destination"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    results = replay(**vars(args))
    (args.destination / "receipt.json").write_text(json.dumps(results, indent=2) + "\n")
    for name, result in results.items():
        print(name, result["exit_code"])
