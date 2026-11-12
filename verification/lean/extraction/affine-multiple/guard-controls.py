#!/usr/bin/env python3
"""Replay the checked affine-multiple variant and its exact scope controls."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess

from zip_lifetimes import lifetime_shapes, load, require, wrong_lifetime

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
ARTIFACTS = ("Funs.lean", "FunsExternal_Template.lean", "Types.lean")
FLAGS = ["-backend", "lean", "-sequential", "-no-progress-bar", "-print-error-emitters", "-split-files"]
FLAG = "BULKSKETCH_AFFINE_MULTIPLE"


def digest(file):
    return sha256(file.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("stock", "variant", "output"):
        parser.add_argument("--" + name, required=True, type=Path)
    args = parser.parse_args()
    original = HERE / "arithmetic.llbc"
    contents = original.read_bytes()
    control_dir = args.output / "wrong-lifetime"
    control_dir.mkdir(parents=True, exist_ok=True)
    altered = control_dir / "arithmetic.llbc"
    altered.write_bytes(wrong_lifetime(contents))
    (args.output / "zip-lifetimes.log").write_text(lifetime_shapes(load(contents)))
    compatible = ROOT / "extraction/affine-splitter"
    cases = (
        ("stock", args.stock, original, False, True, None),
        ("flag-off", args.variant, original, False, True, None),
        ("unchecked", args.variant, original, True, False, None),
        ("checked", args.variant, original, True, True, HERE / "Arithmetic"),
        ("wrong-lifetime", args.variant, altered, True, True, None),
        ("affine-splitter", args.variant, compatible / "arithmetic.llbc", True, True, compatible / "Arithmetic"),
    )

    def run(case):
        name, binary, llbc, enabled, checked, baseline = case
        directory = args.output / name
        directory.mkdir(parents=True, exist_ok=True)
        command = [str(binary), *FLAGS, *(["-checks"] if checked else []),
                   "-dest", str(directory / "generated"), str(llbc)]
        env = {key: value for key, value in os.environ.items() if key != FLAG}
        if enabled:
            env[FLAG] = "1"
        log = directory / "run.log"
        with log.open("w") as handle:
            result = subprocess.run(command, env=env, stdout=handle, stderr=subprocess.STDOUT)
        outputs = {}
        if baseline is not None:
            require(result.returncode == 0, f"{name} failed: {result.returncode}")
            for artifact in ARTIFACTS:
                observed = digest(directory / "generated" / artifact)
                require(observed == digest(baseline / artifact), f"{name} changed {artifact}")
                outputs[artifact] = observed
        else:
            diagnostic = log.read_text()
            original_line = 2084 if name == "stock" else 2120
            require(result.returncode == 1 and "Internal error" in diagnostic
                    and "Source: 'src/decode/affine.rs', lines 119:4-170:1" in diagnostic
                    and f"Compiler source: interp/InterpBorrows.ml, line {original_line}" in diagnostic,
                    "expected checked scope rejection: " + name)
        return name, dict(command=command, environment={FLAG: "1"} if enabled else {},
                          exit_code=result.returncode, input_sha256=digest(llbc), binary_sha256=digest(binary),
                          log_sha256=digest(log), outputs=outputs)

    with ThreadPoolExecutor(max_workers=2) as pool:
        results = dict(pool.map(run, cases))
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
