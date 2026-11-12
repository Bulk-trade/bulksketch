#!/usr/bin/env python3
"""Replay the checked loop erasure variant and its rejection controls."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import shutil
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
BASE = "ab34bd28458a08c150b7cbf1873e59af74588138"
CHARON = "7b462d9159db2ed3015162352183906a30bfafc6"
VARIANT = "checked-shared-loop-erasure-v1"
OWNER_PATCH = "tooling/aeneas-dense-prefix/owner-guard.patch"
SOURCES = ("src/interp/InterpExpansion.ml", "src/symbolic/SymbolicToPureExpressions.ml")
INPUT = "extraction/dense-mul/arithmetic.llbc"
SQUARE = "extraction/dense-square/arithmetic.llbc"
NAMES = ("Types.lean", "Funs.lean")
REJECTIONS = {"mutable-loan-payload", "mutable-consumed-payload", "mutable-given-back-payload",
    "active-child-loan", "registered-continuation", "unregistered-erasure", "level-zero", "level-two",
    "join-ending", "unended-level", "data-continuation", "unchecked"}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(path, *args):
    return subprocess.check_output(["git", *args], cwd=path)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for argument in ("owner-source", "patched-source", "output", "opam-root"):
        parser.add_argument("--" + argument, required=True, type=lambda value: Path(value).resolve())
    parser.add_argument("--opam-switch", default="aeneas-5.3.0")
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    patch = HERE / "shared-loop-erasure.patch"
    parent = (ROOT / OWNER_PATCH).read_bytes()
    if not patch.read_bytes().startswith(parent):
        raise RuntimeError("Dense mul patch lacks the exact existing owner fix")
    for checkout, expected in [(args.owner_source, parent), (args.patched_source, patch.read_bytes())]:
        if git(checkout, "rev-parse", "HEAD").decode().strip() != BASE or \
                git(checkout, "diff", "--binary") != expected:
            raise RuntimeError("wrong translator checkout: " + str(checkout))
    owner = args.owner_source / "src/_build/default/main.exe"
    patched = args.patched_source / "src/_build/default/main.exe"
    commands = []

    def run(name, command, cwd=ROOT):
        command = [str(item) for item in command]
        start = time.monotonic()
        result = subprocess.run(command, cwd=cwd, stdin=subprocess.DEVNULL,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=180)
        log = args.output / (name + ".log")
        log.write_text(result.stdout)
        record = {"name": name, "command": command, "cwd": str(cwd), "exit_code": result.returncode,
                  "elapsed_seconds": time.monotonic() - start, "log_sha256": sha(log)}
        commands.append(record)
        return record, result.stdout

    def translate(name, binary, llbc, checked):
        directory = args.output / name
        directory.mkdir(exist_ok=True)
        command = [binary, "-backend", "lean", "-split-files", "-sequential", "-print-error-emitters"]
        if checked:
            command.append("-checks")
        return run(name, command + ["-dest", directory, ROOT / llbc])

    for path in (INPUT, SQUARE):
        if json.loads((ROOT / path).read_text())["has_errors"] is not False:
            raise RuntimeError("incomplete original LLBC: " + path)
    record, output = translate("owner-only", owner, INPUT, True)
    if record["exit_code"] != 1 or "SymbolicToPureExpressions.ml, line 1288" not in output:
        raise RuntimeError("owner-only variant failed to reproduce level-1 rejection")
    record, output = translate("without-checks", patched, INPUT, False)
    if record["exit_code"] != 1 or "InterpExpansion.ml" not in output or "Unreachable" not in output:
        raise RuntimeError("unchecked original extraction lost its owner rejection")
    extraction, output = translate("original-mul", patched, INPUT, True)
    if extraction["exit_code"] or "Generated the partial file" in output:
        raise RuntimeError("original Dense mul extraction did not complete")
    generated = []
    for name in NAMES:
        path = "extraction/dense-mul/Arithmetic/" + name
        if (args.output / "original-mul" / name).read_bytes() != (ROOT / path).read_bytes():
            raise RuntimeError("preserved Dense mul artifact changed: " + path)
        generated.append({"path": path, "sha256": sha(ROOT / path)})
    record, output = translate("square-control", patched, SQUARE, True)
    if record["exit_code"] or "Generated the partial file" in output or any(
            (args.output / "square-control" / name).read_bytes() !=
            (ROOT / "extraction/dense-square/Arithmetic" / name).read_bytes() for name in NAMES):
        raise RuntimeError("existing Dense square extraction changed")

    guard_dir = args.patched_source / "src/dense_mul_guard_tests"
    guard_dir.mkdir(exist_ok=True)
    guards = sorted((HERE / "guards").iterdir())
    for path in guards:
        shutil.copy2(path, guard_dir / path.name)
    record, output = run("erasure-guards", ["opam", "exec", "--root=" + str(args.opam_root),
        "--switch=" + args.opam_switch, "--", "dune", "exec", "--root", "src", "-j", "2",
        "./dense_mul_guard_tests/dense_mul_guards.exe"], args.patched_source)
    if record["exit_code"] or set(re.findall(r"(?m)^PASS (.+)$", output)) != REJECTIONS | {"shared-owned-region"}:
        raise RuntimeError("erasure guard controls failed")
    regressions = [{"case": "original-mul", "baseline_exit_code": 1, "patched_exit_code": 0, "status": "passed"},
        {"case": "square-control", "status": "passed"}, {"case": "shared-owned-region", "status": "passed"},
        {"case": "without-checks", "exit_code": 1, "status": "expected_rejection_confirmed"}]
    regressions.extend({"case": case, "status": "expected_rejection_confirmed"} for case in sorted(REJECTIONS))
    receipt = {"status": "passed", "variant_id": VARIANT, "base_aeneas_commit": BASE, "charon_commit": CHARON,
        "patch": str(patch.relative_to(ROOT)), "patch_sha256": sha(patch),
        "parent_patch": OWNER_PATCH, "parent_patch_sha256": sha(ROOT / OWNER_PATCH),
        "modified_sources": {p: sha(args.patched_source / p) for p in SOURCES},
        "base_sources": {p: hashlib.sha256(git(args.patched_source, "show", "HEAD:" + p)).hexdigest() for p in SOURCES},
        "unchanged_collapse_guard_source_sha256": sha(args.patched_source / "src/interp/InterpReduceCollapse.ml"),
        "baseline_binary_sha256": sha(owner), "patched_binary_sha256": sha(patched),
        "extraction": {"input": INPUT, "input_sha256": sha(ROOT / INPUT), "required_flags": ["-checks", "-sequential"],
            "command": extraction["command"], "generated": generated, "exit_code": 0},
        "regression_sources": {str(p.relative_to(ROOT)): sha(p) for p in [HERE / "run.py", *guards]},
        "regressions": regressions, "commands": commands, "native_source_changed": False,
        "new_native_coverage_credit_from_tests": 0}
    (HERE / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"status": "passed", "regressions": regressions, "extraction": receipt["extraction"]}, indent=2))


if __name__ == "__main__":
    main()
