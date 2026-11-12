#!/usr/bin/env python3
"""Replay the checked shared expansion variant and its regression controls."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
BASE = "ab34bd28458a08c150b7cbf1873e59af74588138"
CHARON = "7b462d9159db2ed3015162352183906a30bfafc6"
MODIFIED = "src/interp/InterpExpansion.ml"
PREFIX_ROOTS = ("prefix_zip_read", "prefix_stride_read")
GUARDS = {
    "shared-abstraction-owner", "shared-abstraction-child",
    "shared-expression-owner", "shared-expression-child",
    "non-shared-expansion-with-loans",
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(path, *args):
    return subprocess.check_output(["git", *args], cwd=path)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for argument in ("charon", "baseline-aeneas", "patched-aeneas", "patched-source", "output", "opam-root"):
        parser.add_argument("--" + argument, required=True, type=lambda value: Path(value).resolve())
    parser.add_argument("--opam-switch", default="aeneas-5.3.0")
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    for directory, expected in [(args.baseline_aeneas.parent, BASE),
                                (args.patched_source, BASE), (args.charon.parent, CHARON)]:
        if git(directory, "rev-parse", "HEAD").decode().strip() != expected:
            raise RuntimeError("wrong extractor source commit: " + str(directory))
    if git(args.baseline_aeneas.parent, "status", "--porcelain", "--untracked-files=no"):
        raise RuntimeError("baseline Aeneas source differs from its pin")
    patch = HERE / "owner-guard.patch"
    if git(args.patched_source, "diff", "--binary") != patch.read_bytes():
        raise RuntimeError("patched source differs from pinned diff")
    env = dict(os.environ, RUSTUP_TOOLCHAIN="nightly-2026-09-17", CARGO_BUILD_JOBS="1",
               CARGO_TARGET_DIR=str(args.output / "charon-target"))
    commands = []
    regressions = []

    def run(name, command, cwd=ROOT):
        command = [str(item) for item in command]
        start = time.monotonic()
        result = subprocess.run(command, cwd=cwd, env=env, stdin=subprocess.DEVNULL,
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
        return run(name, command + ["-dest", directory, llbc])

    repro_llbc = args.output / "repro.llbc"
    record, _ = run("charon-prefix-repro", [args.charon, "cargo", "--preset=aeneas", "--sysroot=default",
        "--dest-file=" + str(repro_llbc), "--", "--manifest-path", HERE / "tests/Cargo.toml",
        "--lib", "--locked", "--offline"])
    if record["exit_code"] != 0 or json.loads(repro_llbc.read_text())["has_errors"] is not False:
        raise RuntimeError("prefix regression LLBC is incomplete")
    baseline, output = translate("prefix-baseline", args.baseline_aeneas, repro_llbc, True)
    if baseline["exit_code"] != 1 or "InterpExpansion.ml, line 449" not in output or \
            any(root not in output for root in PREFIX_ROOTS):
        raise RuntimeError("baseline failed to reproduce both original owner checks")
    patched, output = translate("prefix-checked", args.patched_aeneas, repro_llbc, True)
    if patched["exit_code"] or "Generated the partial file" in output:
        raise RuntimeError("checked prefix translation did not complete")
    funs = (args.output / "prefix-checked/Funs.lean").read_text()
    for root in PREFIX_ROOTS:
        if not re.search(r"(?m)^def\s+" + root + r"\b", funs):
            raise RuntimeError("missing real prefix body: " + root)
        regressions.append({"case": root, "baseline_exit_code": 1, "patched_exit_code": 0, "status": "passed"})
    record, output = translate("prefix-without-checks", args.patched_aeneas, repro_llbc, False)
    if record["exit_code"] != 1 or "Unreachable" not in output or \
            "InterpExpansion.ml" not in output or any(root not in output for root in PREFIX_ROOTS):
        raise RuntimeError("unchecked mode lost original prefix rejection")
    regressions.append({"case": "without-checks", "exit_code": 1, "status": "expected_rejection_confirmed"})

    guard_dir = args.patched_source / "src/dense_prefix_guard_tests"
    guard_dir.mkdir(exist_ok=True)
    for path in sorted((HERE / "guards").iterdir()):
        shutil.copy2(path, guard_dir / path.name)
    record, output = run("projection-guards", ["opam", "exec", "--root=" + str(args.opam_root),
        "--switch=" + args.opam_switch, "--", "dune", "exec", "--root", "src", "-j", "2",
        "./dense_prefix_guard_tests/dense_prefix_guards.exe", "--", repro_llbc], args.patched_source)
    if record["exit_code"] or set(re.findall(r"(?m)^PASS (.+)$", output)) != GUARDS:
        raise RuntimeError("matching-owner, child or non-shared guard control failed")
    regressions.extend({"case": case, "status": "expected_rejection_confirmed"} for case in sorted(GUARDS))

    record, output = run("rust-value-regressions", ["cargo", "test", "--release", "--locked", "--offline",
        "--manifest-path", HERE / "tests/Cargo.toml", "--target-dir", args.output / "rust-target", "-j2"])
    if record["exit_code"] or "1 passed; 0 failed" not in output:
        raise RuntimeError("Rust prefix values or tail check failed")

    original = ROOT / "extraction/dense-square/arithmetic.llbc"
    if json.loads(original.read_text())["has_errors"] is not False:
        raise RuntimeError("original square LLBC is incomplete")
    record, output = translate("original-square", args.patched_aeneas, original, True)
    if record["exit_code"] or "Generated the partial file" in output:
        raise RuntimeError("original square extraction did not complete")
    generated = []
    for name in ("Types.lean", "Funs.lean"):
        copied = ROOT / "extraction/dense-square/Arithmetic" / name
        if (args.output / "original-square" / name).read_bytes() != copied.read_bytes():
            raise RuntimeError("preserved original extraction differs: " + name)
        generated.append({"path": str(copied.relative_to(ROOT)), "sha256": sha(copied)})
    receipt = {
        "status": "passed", "variant_id": "checked-shared-expansion-owner-v1",
        "base_aeneas_commit": BASE, "charon_commit": CHARON,
        "patch": str(patch.relative_to(ROOT)), "patch_sha256": sha(patch),
        "modified_sources": {MODIFIED: sha(args.patched_source / MODIFIED)},
        "base_sources": {MODIFIED: hashlib.sha256(git(args.patched_source, "show", "HEAD:" + MODIFIED)).hexdigest()},
        "unchanged_collapse_guard_source_sha256": sha(args.patched_source / "src/interp/InterpReduceCollapse.ml"),
        "patched_binary_sha256": sha(args.patched_aeneas), "baseline_binary_sha256": sha(args.baseline_aeneas),
        "extraction": {"input": str(original.relative_to(ROOT)), "input_sha256": sha(original),
            "required_flags": ["-checks", "-sequential"], "command": record["command"],
            "generated": generated, "exit_code": 0},
        "regression_sources": {str(p.relative_to(ROOT)): sha(p) for p in
            [HERE / "run.py", HERE / "tests/Cargo.toml", HERE / "tests/Cargo.lock", HERE / "tests/src/lib.rs",
             *sorted((HERE / "guards").iterdir())]},
        "regressions": regressions, "commands": commands, "native_source_changed": False,
        "new_native_coverage_credit_from_tests": 0,
    }
    (HERE / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"status": "passed", "regressions": regressions, "extraction": receipt["extraction"]}, indent=2))


if __name__ == "__main__":
    main()
