#!/usr/bin/env python3
"""Reproduce the checked immutable-capture frontend patch and its controls.

This is an optional extractor regression suite. Ordinary Lean verification
checks its pinned receipt and generated artifacts without rebuilding OCaml.
No native BulkSketch source is generated or modified by this script.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
BASE = "ab34bd28458a08c150b7cbf1873e59af74588138"
CHARON = "7b462d9159db2ed3015162352183906a30bfafc6"
GUARD = "Joining region abstractions containing shared loans whose shared value contains borrows is not supported yet"
MODIFIED = ["src/interp/InterpJoin.ml", "src/pure/PureUtils.ml", "src/pure/PureMicroPassesLoops.ml"]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--charon", type=Path, required=True)
    parser.add_argument("--baseline-aeneas", type=Path, required=True)
    parser.add_argument("--patched-aeneas", type=Path, required=True)
    parser.add_argument("--patched-source", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    source = args.patched_source.resolve()
    if subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=source, text=True).strip() != BASE:
        raise RuntimeError("wrong Aeneas base commit")
    modified = subprocess.check_output(["git", "diff", "--name-only"], cwd=source, text=True).splitlines()
    if set(modified) != set(MODIFIED):
        raise RuntimeError("unexpected translator source modifications")
    patch = subprocess.check_output(["git", "diff", "--binary"], cwd=source)
    if patch != (HERE / "loop-capture.patch").read_bytes():
        raise RuntimeError("translator diff differs from reviewed patch")
    if subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=args.charon.parent, text=True).strip() != CHARON:
        raise RuntimeError("wrong Charon source pin")
    env = dict(os.environ, RUSTUP_TOOLCHAIN="nightly-2026-09-17", CARGO_BUILD_JOBS="1",
               CARGO_TARGET_DIR=str(args.output / "charon-target"))
    commands = []

    def run(name, command, cwd=ROOT):
        start = time.monotonic()
        result = subprocess.run([str(x) for x in command], cwd=cwd, env=env,
            stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            text=True, timeout=180)
        log = args.output / (name + ".log")
        log.write_text(result.stdout)
        record = {"name": name, "command": [str(x) for x in command], "cwd": str(cwd),
                  "exit_code": result.returncode, "elapsed_seconds": time.monotonic() - start,
                  "log_sha256": sha(log)}
        commands.append(record)
        return record, result.stdout

    outcomes = []
    roots = ["captured_callback", "aliased_shared_capture", "captured_phantom_callback",
             "ordinary_shared_loop", "captured_borrow_result", "nested_mutable_shared_capture",
             "nested_shared_referent_capture", "captured_expandable_referent"]
    positives = set(roots[:5])
    for root in roots:
        directory = args.output / root
        directory.mkdir(exist_ok=True)
        llbc = directory / "input.llbc"
        record, _ = run(root + "-charon", [args.charon, "cargo", "--preset=aeneas", "--sysroot=default",
            "--dest-file=" + str(llbc), "--start-from=aeneas_loop_capture_regression::" + root,
            "--", "--manifest-path", HERE / "tests/Cargo.toml", "--lib", "--locked"])
        if record["exit_code"] or json.loads(llbc.read_text())["has_errors"] is not False:
            raise RuntimeError("incomplete regression extraction: " + root)
        results = {}
        for label, binary in [("baseline", args.baseline_aeneas), ("patched", args.patched_aeneas)]:
            out = directory / label
            out.mkdir(exist_ok=True)
            record, output = run(root + "-" + label,
                [binary, "-backend", "lean", "-split-files", "-checks", "-sequential", "-dest", out, llbc])
            results[label] = record["exit_code"]
            if label == "patched" and root in positives:
                if record["exit_code"] or "Generated the partial file" in output or "Error" in output:
                    raise RuntimeError("required positive failed: " + root)
                text = (out / "Funs.lean").read_text()
                if not re.search(r"^def\s+" + re.escape(root) + r"\b", text, re.MULTILINE) or \
                        re.search(r"\b(sorry|axiom|admit|native_decide)\b", text):
                    raise RuntimeError("positive missing its real definition: " + root)
            if label == "baseline" and root == "captured_callback":
                if not record["exit_code"] or GUARD not in output:
                    raise RuntimeError("baseline did not reproduce the captured-loan guard")
        if root not in positives and bool(results["baseline"]) != bool(results["patched"]):
            raise RuntimeError("indirect graph control changed acceptance: " + root)
        outcomes.append({"case": root, "baseline_exit_code": results["baseline"],
                         "patched_exit_code": results["patched"], "status": "passed",
                         "meaning": "required positive" if root in positives else "unchanged indirect graph control"})
    out = args.output / "without-checks"
    out.mkdir(exist_ok=True)
    record, output = run("without-checks", [args.patched_aeneas, "-backend", "lean", "-split-files",
        "-sequential", "-dest", out, args.output / "captured_callback/input.llbc"])
    if not record["exit_code"] or GUARD not in output:
        raise RuntimeError("unchecked mode unexpectedly accepted the new capture case")
    outcomes.append({"case": "without-checks", "exit_code": record["exit_code"],
                     "status": "expected_rejection_confirmed"})
    for path in sorted((HERE / "tests/negative").glob("*.rs")):
        record, output = run(path.stem + "-rust-borrow-rejection", ["rustc", "--edition=2024",
            "--crate-type=lib", "--emit=metadata", "-o", args.output / (path.stem + ".rmeta"), path])
        if not record["exit_code"] or "E0502" not in output:
            raise RuntimeError("invalid aliasing program was not rejected: " + path.name)
        outcomes.append({"case": path.stem, "status": "expected_rust_borrow_rejection_confirmed"})
    record, _ = run("rust-value-regressions", ["cargo", "test", "--release", "--locked",
        "--manifest-path", HERE / "tests/Cargo.toml", "--target-dir", args.output / "rust-target", "-j2"])
    if record["exit_code"]:
        raise RuntimeError("Rust value regressions failed")
    original = ROOT / "extraction/canonical-arithmetic/inverse-pilot/arithmetic.llbc"
    native_out = args.output / "original-inverse"
    native_out.mkdir(exist_ok=True)
    command = [args.patched_aeneas, "-backend", "lean", "-split-files", "-checks", "-sequential",
               "-dest", native_out, original]
    record, output = run("original-inverse", command)
    if record["exit_code"] or "Generated the partial file" in output or "Error" in output:
        raise RuntimeError("original inverse extraction did not complete")
    generated = []
    for name in ["Types.lean", "Funs.lean"]:
        copied = ROOT / "extraction/inverse-wrappers/Arithmetic" / name
        if (native_out / name).read_bytes() != copied.read_bytes():
            raise RuntimeError("committed original extraction differs: " + name)
        generated.append({"path": str(copied.relative_to(ROOT)), "sha256": sha(copied)})
    receipt = {"status": "passed", "base_aeneas_commit": BASE, "charon_commit": CHARON,
        "patch": "tooling/aeneas-loop-capture/loop-capture.patch", "patch_sha256": sha(HERE / "loop-capture.patch"),
        "modified_sources": {p: sha(source / p) for p in MODIFIED},
        "base_sources": {p: hashlib.sha256(subprocess.check_output(["git", "show", "HEAD:" + p], cwd=source)).hexdigest() for p in MODIFIED},
        "unchanged_collapse_guard_source_sha256": sha(source / "src/interp/InterpReduceCollapse.ml"),
        "patched_binary_sha256": sha(args.patched_aeneas), "baseline_binary_sha256": sha(args.baseline_aeneas),
        "extraction": {"input": str(original.relative_to(ROOT)), "input_sha256": sha(original),
            "required_flags": ["-checks", "-sequential"], "command": [str(x) for x in command],
            "generated": generated, "exit_code": 0},
        "regressions": outcomes, "commands": commands, "native_source_changed": False,
        "regression_sources": {str(p.relative_to(ROOT)): sha(p) for p in
            [HERE / "run.py", HERE / "tests/Cargo.toml", HERE / "tests/Cargo.lock",
             *sorted((HERE / "tests").rglob("*.rs"))]},
        "new_native_coverage_credit_from_tests": 0,
        "trust_boundary": "Reviewed Aeneas frontend patch under mandatory enabled sanity/frozen-context checks; not a kernel theorem of compiler correctness."}
    (HERE / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"status": "passed", "patch_sha256": receipt["patch_sha256"],
                      "regressions": outcomes, "receipt": str(HERE / "receipt.json")}, indent=2))


if __name__ == "__main__":
    main()
