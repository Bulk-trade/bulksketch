#!/usr/bin/env python3
"""Reproduce checked Dense modular square extraction and its negative controls."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import subprocess

from project import CONTROLS, ENVIRONMENT, EXTRACTION, FLAGS, NAMES, PATCH, RAW, ROOT, check, require, sha, shared


def git(path, *args):
    return subprocess.check_output(["git", *args], cwd=path)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("patched-source", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    check()
    stock = ROOT / "tooling/aeneas"
    patched = args.patched_source.resolve()
    output = args.output.resolve()
    require(git(stock, "rev-parse", "HEAD").decode().strip() == shared.AENEAS
            and not git(stock, "diff", "HEAD", "--binary"), "pinned Aeneas sources changed")
    require(git(patched, "rev-parse", "HEAD").decode().strip() == shared.AENEAS
            and git(patched, "diff", "HEAD", "--binary") == (ROOT / PATCH).read_bytes(),
            "Dense reducer patched sources differ")
    charon = patched / "charon"
    require(git(charon, "rev-parse", "HEAD").decode().strip() == shared.CHARON
            and not git(charon, "diff", "HEAD", "--binary"), "pinned Charon sources changed")
    output.mkdir(parents=True, exist_ok=False)

    def run(item):
        name, (enabled, checked, expected) = item
        destination = output / name
        destination.mkdir()
        binary = stock if name in ("stock", "portable-xor-stock") else patched
        input_path = ROOT / ("extraction/portable-xor/arithmetic.llbc" if name.startswith("portable-xor")
                            else EXTRACTION / "arithmetic.llbc")
        env = os.environ.copy()
        env.pop("BULKSKETCH_DENSE_REDUCER", None)
        if enabled:
            env.update(ENVIRONMENT)
        command = [str(binary / "src/_build/default/main.exe"), *FLAGS, *(["-checks"] if checked else []),
                   "-dest", str(destination), str(input_path)]
        process = subprocess.run(command, env=env, cwd=ROOT, capture_output=True, timeout=240)
        text = (process.stdout + process.stderr).decode()
        (output / (name + ".log")).write_text(text)
        require(process.returncode == expected, "Dense reducer replay exit changed: " + name)
        if expected:
            require("Could not match the contexts" in text and "lines 213:16-217:17" in text,
                    "Dense reducer replay lost original negative outcome: " + name)
        else:
            require("Generated the partial file" not in text and {file.name for file in destination.iterdir()} == set(NAMES),
                    "Dense reducer successful replay was incomplete: " + name)
        return name, {"command": command, "exit_code": process.returncode, "environment": ENVIRONMENT if enabled else {},
                      "input_sha256": sha(input_path), "outputs": {name: sha(destination / name) for name in NAMES}}

    with ThreadPoolExecutor(max_workers=2) as pool:
        results = dict(pool.map(run, CONTROLS.items()))
    exact = {name: sha(ROOT / RAW / name) for name in NAMES}
    require(results["checked"]["outputs"] == exact and results["replay"]["outputs"] == exact,
            "Dense reducer original generated files differ")
    require(results["portable-xor"]["outputs"] == results["portable-xor-stock"]["outputs"],
            "Dense reducer changed an unrelated Portable XOR capture")
    (output / "commands.json").write_text(json.dumps(results, indent=2) + "\n")
    print(json.dumps({name: row["exit_code"] for name, row in results.items()}, indent=2))


if __name__ == "__main__":
    main()
