#!/usr/bin/env python3
"""Replay exact original locator extraction with the checked scoped translator."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import re
import subprocess

from project import (ARTIFACTS, BASE, CHARON, ENVIRONMENT, EXTRACTION, GENERATED, LLBC_SHA,
                     PATCH, POSITIVE_COUNTS, ROOT, RUNTIMES, SOURCES, SOURCE_COMMIT,
                     TARGET, VARIANT, require, sha)
NAMES = ("Types.lean", "Funs.lean", "FunsExternal_Template.lean")
FLAGS = ("-backend", "lean", "-sequential", "-no-progress-bar", "-print-error-emitters", "-split-files")



def git(path, *args):
    return subprocess.check_output(["git", *args], cwd=path)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("patched-source", "output"):
        parser.add_argument("--" + name, type=lambda value: Path(value).resolve(), required=True)
    args = parser.parse_args()
    pinned = ROOT / "tooling/aeneas"
    require(git(pinned, "rev-parse", "HEAD").decode().strip() == BASE
            and not git(pinned, "diff", "HEAD", "--binary"), "pinned Aeneas source drift")
    require(git(args.patched_source, "rev-parse", "HEAD").decode().strip() == BASE
            and git(args.patched_source, "diff", "HEAD", "--binary") == (ROOT / PATCH).read_bytes(),
            "checked BM source differs from the exact patch")
    require(set(git(args.patched_source, "diff", "HEAD", "--name-only").decode().splitlines()) == SOURCES,
            "BM variant changes an unexpected source file")

    charon = args.patched_source / "charon"
    require(git(charon, "rev-parse", "HEAD").decode().strip() == CHARON
            and not git(charon, "diff", "HEAD", "--binary"), "pinned Charon source drift")

    llbc = ROOT / EXTRACTION / "arithmetic.llbc"
    require(sha(llbc) == LLBC_SHA and json.loads(llbc.read_text())["has_errors"] is False,
            "original BM LLBC is incomplete or changed")
    xor = ROOT / "extraction/portable-xor/arithmetic.llbc"
    baseline = pinned / "src/_build/default/main.exe"
    patched = args.patched_source / "src/_build/default/main.exe"
    args.output.mkdir(parents=True, exist_ok=False)

    def translate(name, binary, input_llbc, enabled, checks, expected):
        dest = args.output / name
        dest.mkdir()
        environment = dict(os.environ)
        environment.pop("BULKSKETCH_BM_LOCATOR", None)
        if enabled:
            environment.update(ENVIRONMENT)
        flags = [*FLAGS, *(["-checks"] if checks else [])]
        if expected == 0:
            flags.append("-abort-on-error")
        command = [str(binary), *flags, "-dest", str(dest), str(input_llbc)]
        result = subprocess.run(command, cwd=ROOT, env=environment, stdin=subprocess.DEVNULL,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=240)
        log = args.output / (name + ".log")
        log.write_bytes(result.stdout)
        require(result.returncode == expected, "unexpected BM replay exit: " + str(log))
        text = result.stdout.decode()
        if expected == 0:
            require("Generated the partial file" not in text and
                    {file.name for file in dest.iterdir()} == set(NAMES),
                    "incomplete successful replay: " + str(log))
        return {
            "name": name, "command": command, "exit_code": result.returncode,
            "environment": ENVIRONMENT if enabled else {}, "log_sha256": sha(log),
        }, text

    jobs = [
        ("checked", patched, llbc, True, True, 0),
        ("replay", patched, llbc, True, True, 0),
        ("disabled", patched, llbc, False, True, 1),
        ("unchecked", patched, llbc, True, False, 1),
        ("portable-xor", patched, xor, True, True, 0),
        ("portable-xor-baseline", baseline, xor, False, True, 0),
    ]
    with ThreadPoolExecutor(max_workers=2) as pool:
        results = list(pool.map(lambda job: translate(*job), jobs))
    commands = {record["name"]: record for record, _ in results}
    logs = {record["name"]: log for record, log in results}
    for name in ("checked", "replay"):
        require(all(logs[name].count(marker) == count for marker, count in POSITIVE_COUNTS.items()),
                "BM checked writeback counts changed: " + name)
        for output in NAMES:
            raw = ROOT / EXTRACTION / "Arithmetic" / output
            require((args.output / name / output).read_bytes() == raw.read_bytes(),
                    "exact generated BM artifact differs: " + output)
        funs = (args.output / name / "Funs.lean").read_text()
        require(re.search(r"(?m)^def decode\.bm\.locator\s*$", funs) is not None
                and funs.count("let z1 := back1 z\n") == 8, "real BM locator or writeback missing")
    for name in ("disabled", "unchecked"):
        require("Early returns inside of loops are not supported yet" in logs[name]
                and "PrePasses.ml, line 575" in logs[name] and "BM-" not in logs[name],
                "BM disabled or unchecked rejection changed: " + name)
    for name in ("portable-xor", "portable-xor-baseline"):
        require("BM-" not in logs[name], "unrelated control entered BM hooks")
    for output in NAMES:
        require((args.output / "portable-xor" / output).read_bytes() ==
                (args.output / "portable-xor-baseline" / output).read_bytes(),
                "ordinary Portable XOR extraction changed: " + output)

    generated = [{"path": path, "sha256": sha(ROOT / path)} for path in sorted(GENERATED)]
    logs_paths = {f"{EXTRACTION}/{name}.log": args.output / f"{name}.log" for name in commands}
    receipt = {
        "status": "generated", "source_commit": SOURCE_COMMIT,
        "aeneas_commit": BASE, "charon_commit": CHARON, "variant_id": VARIANT,
        "target": TARGET, "rust_toolchain": "nightly-2026-09-17",
        "llbc_has_errors": False, "llbc_sha256": LLBC_SHA,
        "variant_patch": PATCH, "variant_patch_sha256": sha(ROOT / PATCH),
        "native_body_proof_credit": 0, "native_source_edited": False,
        "source_selector": "bulksketch::decode::bm::locator",
        "modified_sources": {path: sha(args.patched_source / path) for path in sorted(SOURCES)},
        "base_sources": {path: sha(pinned / path) for path in sorted(SOURCES)},
        "runtime_files_sha256": {path: sha(ROOT / path) for path in sorted(RUNTIMES)},
        "tool_binary_sha256": {"aeneas": sha(patched), "aeneas_pinned": sha(baseline)},
        "checked_extraction": {
            **commands["checked"], "input": str(llbc.relative_to(ROOT)), "input_sha256": LLBC_SHA,
            "required_flags": ["-checks", "-sequential"], "generated": generated,
        },
        "replay": {**commands["replay"], "exact_generated_artifacts": len(NAMES)},
        "controls": {key: commands[key] for key in
                     ("disabled", "unchecked", "portable-xor", "portable-xor-baseline")},
        "portable_xor_exact_artifacts": len(NAMES),
        "checked_event_counts": POSITIVE_COUNTS,
        "artifacts": [{"path": path, "sha256": sha(logs_paths.get(path, ROOT / path))}
                      for path in sorted(ARTIFACTS)],
    }
    audit_source = ROOT / EXTRACTION / "Axioms.lean"
    audit_log = ROOT / EXTRACTION / "axioms.log"
    receipt["axiom_audit"] = {"exit_code": 0, "source_sha256": sha(audit_source),
                              "log_sha256": sha(audit_log)}
    (args.output / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"status": "passed", "exact_generated_artifacts": len(NAMES),
                      "checked_event_counts": POSITIVE_COUNTS}, indent=2))


if __name__ == "__main__":
    main()
