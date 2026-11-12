#!/usr/bin/env python3
"""Replay the checked ended-scalar context matcher and its regression controls."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
BASE = "ab34bd28458a08c150b7cbf1873e59af74588138"
CHARON = "7b462d9159db2ed3015162352183906a30bfafc6"
VARIANT = "checked-ended-shared-scalar-v1"
SOURCE = "src/interp/InterpMatchCtxs.ml"
ORIGINAL = "extraction/portable-horner"
ROOT_NAME = "backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.horner_many"
GENERATED = ("Types.lean", "Funs.lean", "TypesExternal_Template.lean", "FunsExternal_Template.lean")
ACCEPT = {"same-scalar-mapping", "same-scalar-equivalence"}
REJECT = {"unequal-symbolic-id", "distinct-child-payload", "nonempty-child-mismatch",
          "loan-child", "nonscalar-metadata", "same-scalar-unchecked"}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(path, *args):
    return subprocess.check_output(["git", *args], cwd=path)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for key in ("charon-source", "baseline-source", "patched-source", "opam-root", "output"):
        parser.add_argument("--" + key, required=True, type=lambda value: Path(value).resolve())
    parser.add_argument("--opam-switch", default="aeneas-5.3.0")
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    patch = HERE / "ended-shared-scalar.patch"
    for source, revision, expected in ((args.baseline_source, BASE, b""),
            (args.patched_source, BASE, patch.read_bytes()), (args.charon_source, CHARON, b"")):
        if git(source, "rev-parse", "HEAD").decode().strip() != revision or \
                git(source, "diff", "--binary") != expected or git(source, "diff", "--cached"):
            raise RuntimeError("wrong pinned checkout: " + str(source))
    charon = args.charon_source / "bin/charon"
    baseline = args.baseline_source / "src/_build/default/main.exe"
    patched = args.patched_source / "src/_build/default/main.exe"
    env = dict(os.environ, RUSTUP_TOOLCHAIN="nightly-2026-09-17", CARGO_BUILD_JOBS="1",
               CARGO_TARGET_DIR=str(args.output / "charon-target"))
    commands = []
    regressions = []

    def run(name, command, expected, cwd=ROOT):
        command = [str(item) for item in command]
        result = subprocess.run(command, cwd=cwd, env=env, stdin=subprocess.DEVNULL,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                text=True, timeout=180)
        log = args.output / (name + ".log")
        log.write_text(result.stdout)
        commands.append({"name": name, "command": command, "cwd": str(cwd),
                         "exit_code": result.returncode, "log_sha256": sha(log)})
        if result.returncode != expected:
            raise RuntimeError("unexpected exit, see " + str(log))
        return result.stdout

    def translate(name, binary, llbc, expected, checked=True):
        destination = args.output / name
        destination.mkdir(exist_ok=True)
        command = [binary, "-backend", "lean", "-split-files", "-sequential", "-print-error-emitters"]
        if checked:
            command.append("-checks")
        output = run(name, command + ["-dest", destination, llbc], expected)
        if expected and ("Could not match the contexts" not in output or
                         "InterpJoin.ml, line 1571" not in output):
            raise RuntimeError("unexpected rejection: " + name)
        if not expected and ("Generated the partial file" in output or
                             not (destination / "Funs.lean").is_file()):
            raise RuntimeError("incomplete checked extraction: " + name)
        return destination

    fixture = args.output / "repro.llbc"
    run("charon-fixture", [charon, "cargo", "--preset=aeneas", "--sysroot=default",
        "--dest-file=" + str(fixture), "--", "--manifest-path", HERE / "tests/Cargo.toml",
        "--lib", "--locked", "--offline"], 0)
    original = ROOT / ORIGINAL / "arithmetic.llbc"
    for llbc in (fixture, original):
        if json.loads(llbc.read_text())["has_errors"] is not False:
            raise RuntimeError("incomplete LLBC: " + str(llbc))

    pinned_fixture = translate("fixture-baseline", baseline, fixture, 1)
    checked_fixture = translate("fixture-checked", patched, fixture, 0)
    translate("fixture-without-checks", patched, fixture, 1, checked=False)
    left = (pinned_fixture / "Funs.lean").read_text()
    right = (checked_fixture / "Funs.lean").read_text()
    for name in ("zip_without_split_loop.body", "zip_without_split_loop", "zip_without_split"):
        pattern = r"(?ms)^/--(?:(?!^/--).)*?^def\s+" + re.escape(name) + r"\s.*?(?=^/--|^end )"
        old = re.search(pattern, left)
        new = re.search(pattern, right)
        if not old or not new or old.group() != new.group():
            raise RuntimeError("ordinary Zip control changed: " + name)
    if not re.search(r"(?m)^def\s+split_then_zip\s", right):
        raise RuntimeError("missing real fixture body")
    regressions.extend([
        {"case": "split-then-zip", "baseline_exit_code": 1, "patched_exit_code": 0, "status": "passed"},
        {"case": "zip-without-split", "status": "passed"},
        {"case": "without-checks", "exit_code": 1, "status": "expected_rejection_confirmed"},
    ])
    translate("original-baseline", baseline, original, 1)
    completed = translate("original-horner", patched, original, 0)
    if not re.search(r"(?m)^def\s+" + re.escape(ROOT_NAME) + r"\s", (completed / "Funs.lean").read_text()):
        raise RuntimeError("missing real original Horner body")
    generated = []
    for name in GENERATED:
        path = f"{ORIGINAL}/Arithmetic/{name}"
        if (completed / name).read_bytes() != (ROOT / path).read_bytes():
            raise RuntimeError("original generated artifact changed: " + path)
        generated.append({"path": path, "sha256": sha(ROOT / path)})
    regressions.append({"case": "original-horner", "baseline_exit_code": 1,
                        "patched_exit_code": 0, "status": "passed"})

    guard_dir = args.patched_source / "src/horner_match_guard_tests"
    guard_dir.mkdir(exist_ok=True)
    guards = sorted((HERE / "guards").iterdir())
    for path in guards:
        shutil.copy2(path, guard_dir / path.name)
    output = run("context-matcher-guards", ["opam", "exec", "--root=" + str(args.opam_root),
        "--switch=" + args.opam_switch, "--", "dune", "exec", "--root", "src", "-j", "2",
        "./horner_match_guard_tests/horner_match_guards.exe", "--", fixture], 0, args.patched_source)
    if set(re.findall(r"(?m)^PASS (.+)$", output)) != ACCEPT | REJECT:
        raise RuntimeError("context matcher guard coverage incomplete")
    regressions.extend({"case": name, "status": "passed" if name in ACCEPT else
                        "expected_rejection_confirmed"} for name in sorted(ACCEPT | REJECT))
    sources = [HERE / "run.py", HERE / "tests/Cargo.toml", HERE / "tests/Cargo.lock",
               HERE / "tests/src/lib.rs", *guards]
    receipt = {"status": "passed", "variant_id": VARIANT, "base_aeneas_commit": BASE,
        "charon_commit": CHARON, "patch": str(patch.relative_to(ROOT)), "patch_sha256": sha(patch),
        "modified_sources": {SOURCE: sha(args.patched_source / SOURCE)},
        "base_sources": {SOURCE: hashlib.sha256(git(args.patched_source, "show", "HEAD:" + SOURCE)).hexdigest()},
        "baseline_binary_sha256": sha(baseline), "patched_binary_sha256": sha(patched),
        "charon_binary_sha256": sha(charon), "extraction": {
            "input": str(original.relative_to(ROOT)), "input_sha256": sha(original),
            "required_flags": ["-checks", "-sequential"],
            "command": next(record["command"] for record in commands if record["name"] == "original-horner"),
            "generated": generated, "exit_code": 0},
        "regression_sources": {str(path.relative_to(ROOT)): sha(path) for path in sources},
        "regressions": regressions, "commands": commands, "native_source_changed": False,
        "new_native_coverage_credit_from_tests": 0}
    (args.output / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"status": "passed", "regressions": regressions}, indent=2))


if __name__ == "__main__":
    main()
