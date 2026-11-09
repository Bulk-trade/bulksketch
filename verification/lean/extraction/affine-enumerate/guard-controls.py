#!/usr/bin/env python3
"""Replay affine enumeration and verify exact scope and control-flow rejections."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
import json
from pathlib import Path
import subprocess

from control_flow import altered_capture, check_return_place, enumerate_body, frozen_capture, require

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
ARTIFACTS = ("Funs.lean", "FunsExternal_Template.lean", "Types.lean")
FLAGS = ["-backend", "lean", "-checks", "-sequential", "-no-progress-bar", "-print-error-emitters", "-split-files"]
REJECTION = "Continue to outer loops are not supported yet"
GUARDS = ("wrong-name", "wrong-span", "wrong-cleanup", "wrong-break", "wrong-constructor")


def digest(file):
    return sha256(file.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("stock", "variant", "output"):
        parser.add_argument("--" + name, required=True, type=Path)
    args = parser.parse_args()
    original = HERE / "arithmetic.llbc"
    capture = frozen_capture(original.read_bytes())
    _, body = enumerate_body(capture)
    inputs = {}
    for name in (*GUARDS, "missing-return-assignment"):
        directory = args.output / name
        directory.mkdir(parents=True, exist_ok=True)
        altered = directory / "arithmetic.llbc"
        altered.write_bytes(altered_capture(capture, name))
        inputs[name] = altered

    message = check_return_place(body)
    good_log = args.output / "return-place.log"
    good_log.write_text(message + "\n")
    missing = inputs["missing-return-assignment"]
    _, missing_body = enumerate_body(json.loads(missing.read_bytes()))
    try:
        check_return_place(missing_body)
    except ValueError as error:
        diagnostic = str(error)
        require(diagnostic == "return 1188 reachable without a fresh result assignment", diagnostic)
    else:
        raise ValueError("missing original return assignment was accepted")
    bad_log = args.output / "missing-return-assignment.log"
    bad_log.write_text(diagnostic + "\n")

    cases = [("stock", args.stock, original, 1, HERE / "Arithmetic"),
             ("checked", args.variant, original, 0, HERE / "Arithmetic"),
             ("unchecked", args.variant, original, 1, HERE / "Arithmetic")]
    cases += [(name, args.variant, inputs[name], 1, HERE / "Arithmetic") for name in GUARDS]
    for name in ("root-enumerate-affine", "affine-splitter"):
        baseline = ROOT / "extraction" / name
        cases.append((name, args.variant, baseline / "arithmetic.llbc", 0, baseline / "Arithmetic"))

    def run(case):
        name, binary, source, expected, baseline = case
        directory = args.output / name
        output = directory / "generated"
        directory.mkdir(parents=True, exist_ok=True)
        flags = [flag for flag in FLAGS if flag != "-checks" or name != "unchecked"]
        command = [str(binary), *flags, "-dest", str(output), str(source)]
        log = directory / "run.log"
        with log.open("w") as handle:
            result = subprocess.run(command, stdout=handle, stderr=subprocess.STDOUT)
        require(result.returncode == expected, f"{name} exited {result.returncode}, expected {expected}")
        outputs = {}
        if expected:
            require(REJECTION in log.read_text(), "control missed original rejection: " + name)
        else:
            for artifact in ARTIFACTS:
                observed = digest(output / artifact)
                require(observed == digest(baseline / artifact), "stock output differs: " + name + "/" + artifact)
                outputs[artifact] = observed
        return name, {"command": command, "exit_code": result.returncode, "binary_sha256": digest(binary),
                      "input_sha256": digest(source), "log_sha256": digest(log), "outputs": outputs}

    with ThreadPoolExecutor(max_workers=2) as executor:
        receipts = dict(executor.map(run, cases))
    receipts["return-place"] = {"input_sha256": digest(original), "log_sha256": digest(good_log)}
    receipts["missing-return-assignment"] = {"input_sha256": digest(missing), "log_sha256": digest(bad_log)}
    print(json.dumps(receipts, indent=2))


if __name__ == "__main__":
    main()
