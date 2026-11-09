#!/usr/bin/env python3
"""Check source-linked generated body refinements under the recorded tool/runtime TCB."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
BRIDGE = ROOT / "bridge"
AUDIT = BRIDGE / "audit"
RESULTS = AUDIT / "results"
CHAIN = "leanprover/lean4:v4.35.0"
ENV = dict(os.environ, CI="1", MATHLIB_NO_CACHE_ON_UPDATE="1", LEAN_NUM_THREADS="2")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(name, args, timeout=180, cwd=BRIDGE):
    start = time.monotonic()
    try:
        result = subprocess.run(args, cwd=cwd, env=ENV, stdin=subprocess.DEVNULL,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                text=True, timeout=timeout)
    except subprocess.TimeoutExpired as error:
        output = error.stdout or ""
        if isinstance(output, bytes):
            output = output.decode(errors="replace")
        (RESULTS / (name + ".log")).write_text(output)
        raise
    (RESULTS / (name + ".log")).write_text(result.stdout)
    if result.returncode:
        raise RuntimeError(name + " failed with exit " + str(result.returncode) + ":\n" + result.stdout[-4000:])
    return {"name": name, "command": args, "cwd": str(cwd), "exit_code": 0,
            "elapsed_seconds": time.monotonic() - start}, result.stdout


def check_dense_prefix_variant(variant, receipt, runtime, runtime_head, linkage):
    """Validate the narrow shared-owner patch separately from capture-v1."""
    directory = "tooling/aeneas-dense-prefix/"
    source = "src/interp/InterpExpansion.ml"
    patch = directory + "owner-guard.patch"
    input_path = "extraction/dense-square/arithmetic.llbc"
    generated = {"extraction/dense-square/Arithmetic/" + name
                 for name in ("Types.lean", "Funs.lean")}
    tests = {directory + name for name in ("run.py", "tests/Cargo.toml",
             "tests/Cargo.lock", "tests/src/lib.rs", "guards/dune", "guards/dense_prefix_guards.ml")}
    extraction = receipt["extraction"]
    if receipt["status"] != "passed" or receipt["variant_id"] != variant["id"] or \
            receipt["native_source_changed"] is not False or \
            receipt["new_native_coverage_credit_from_tests"] != 0 or \
            variant["receipt"] != directory + "receipt.json" or \
            receipt["base_aeneas_commit"] != runtime_head or variant["base_commit"] != runtime_head or \
            receipt["charon_commit"] != linkage["charon_commit"] or \
            variant["mandatory_checks"] is not True or receipt["patch"] != patch or \
            variant["patch"] != patch or receipt["patch_sha256"] != variant["patch_sha256"] or \
            sha(ROOT / patch) != variant["patch_sha256"] or \
            set(receipt["modified_sources"]) != {source} or \
            receipt["base_sources"] != {source: sha(runtime / source)} or \
            re.findall(r"(?m)^diff --git a/(\S+) b/(\S+)$", (ROOT / patch).read_text()) != [(source, source)] or \
            sha(runtime / "src/interp/InterpReduceCollapse.ml") != receipt["unchanged_collapse_guard_source_sha256"]:
        raise RuntimeError("dense-prefix variant lost pinned provenance")
    if extraction["input"] != input_path or sha(ROOT / input_path) != extraction["input_sha256"] or \
            extraction["exit_code"] != 0 or set(extraction["required_flags"]) != {"-checks", "-sequential"} or \
            not set(extraction["required_flags"]) <= set(extraction["command"]) or \
            len(extraction["generated"]) != len(generated) or \
            {item["path"] for item in extraction["generated"]} != generated or \
            any(sha(ROOT / item["path"]) != item["sha256"] for item in extraction["generated"]):
        raise RuntimeError("dense-prefix variant lost checks-enabled original extraction")
    if set(receipt["regression_sources"]) != tests or \
            any(sha(ROOT / path) != digest for path, digest in receipt["regression_sources"].items()):
        raise RuntimeError("dense-prefix regression sources changed")

    successes = {"prefix_zip_read", "prefix_stride_read"}
    rejections = {"without-checks", "shared-abstraction-owner", "shared-abstraction-child",
                  "shared-expression-owner", "shared-expression-child", "non-shared-expansion-with-loans"}
    cases = {item["case"]: item for item in receipt["regressions"]}
    commands = {item["name"]: item for item in receipt["commands"]}
    if set(cases) != successes | rejections or len(cases) != len(receipt["regressions"]) or \
            any(cases[key]["status"] != "passed" or cases[key]["baseline_exit_code"] != 1 or
                cases[key]["patched_exit_code"] != 0 for key in successes) or \
            any(cases[key]["status"] != "expected_rejection_confirmed" for key in rejections) or \
            cases["without-checks"]["exit_code"] != 1 or \
            commands["projection-guards"]["exit_code"] != 0 or commands["rust-value-regressions"]["exit_code"] != 0 or \
            commands["original-square"]["command"] != extraction["command"] or \
            commands["original-square"]["exit_code"] != 0:
        raise RuntimeError("dense-prefix regression matrix is incomplete")


def check_dense_mul_variant(variant, receipt, runtime, runtime_head, linkage):
    """Check the cumulative variant without widening the prior owner-only gate."""
    directory = "tooling/aeneas-dense-mul/"
    patch = directory + "shared-loop-erasure.patch"
    parent = "tooling/aeneas-dense-prefix/owner-guard.patch"
    sources = {"src/interp/InterpExpansion.ml", "src/symbolic/SymbolicToPureExpressions.ml"}
    input_path = "extraction/dense-mul/arithmetic.llbc"
    output = {"extraction/dense-mul/Arithmetic/" + name for name in ("Types.lean", "Funs.lean")}
    guard_sources = {directory + name for name in ("run.py", "guards/dune", "guards/dense_mul_guards.ml")}
    parent_receipt = json.loads((ROOT / "tooling/aeneas-dense-prefix/receipt.json").read_text())
    if (receipt["status"] != "passed" or receipt["variant_id"] != variant["id"] or
            receipt["native_source_changed"] is not False or receipt["new_native_coverage_credit_from_tests"] != 0 or
            variant["receipt"] != directory + "receipt.json" or variant["base_commit"] != runtime_head or
            receipt["base_aeneas_commit"] != runtime_head or receipt["charon_commit"] != linkage["charon_commit"] or
            variant["mandatory_checks"] is not True or receipt["patch"] != patch or variant["patch"] != patch or
            receipt["patch_sha256"] != variant["patch_sha256"] or sha(ROOT / patch) != variant["patch_sha256"] or
            receipt["parent_patch"] != parent or receipt["parent_patch_sha256"] != sha(ROOT / parent) or
            receipt["parent_patch_sha256"] != parent_receipt["patch_sha256"] or
            receipt["baseline_binary_sha256"] != parent_receipt["patched_binary_sha256"] or
            not (ROOT / patch).read_bytes().startswith((ROOT / parent).read_bytes()) or
            set(receipt["modified_sources"]) != sources or
            receipt["base_sources"] != {source: sha(runtime / source) for source in sources} or
            sorted(re.findall(r"(?m)^diff --git a/(\S+) b/(\S+)$", (ROOT / patch).read_text())) !=
            [(source, source) for source in sorted(sources)] or
            sha(runtime / "src/interp/InterpReduceCollapse.ml") != receipt["unchanged_collapse_guard_source_sha256"]):
        raise RuntimeError("dense-mul variant lost pinned provenance")
    extraction = receipt["extraction"]
    if (extraction["input"] != input_path or sha(ROOT / input_path) != extraction["input_sha256"] or
            extraction["exit_code"] != 0 or set(extraction["required_flags"]) != {"-checks", "-sequential"} or
            not set(extraction["required_flags"]) <= set(extraction["command"]) or
            len(extraction["generated"]) != len(output) or
            {item["path"] for item in extraction["generated"]} != output or
            any(sha(ROOT / item["path"]) != item["sha256"] for item in extraction["generated"])):
        raise RuntimeError("dense-mul variant lost checked original extraction")
    if (set(receipt["regression_sources"]) != guard_sources or
            any(sha(ROOT / path) != digest for path, digest in receipt["regression_sources"].items())):
        raise RuntimeError("dense-mul regression sources changed")

    positives = {"original-mul", "square-control", "shared-owned-region"}
    negatives = {"without-checks", "active-child-loan", "data-continuation", "join-ending", "level-two",
                 "level-zero", "mutable-consumed-payload", "mutable-given-back-payload", "mutable-loan-payload",
                 "registered-continuation", "unchecked", "unended-level", "unregistered-erasure"}
    expected_codes = {"owner-only": 1, "without-checks": 1, "original-mul": 0, "square-control": 0, "erasure-guards": 0}
    cases = {item["case"]: item for item in receipt["regressions"]}
    commands = {item["name"]: item for item in receipt["commands"]}
    if (set(cases) != positives | negatives or len(cases) != len(receipt["regressions"]) or
            any(cases[key]["status"] != "passed" for key in positives) or
            any(cases[key]["status"] != "expected_rejection_confirmed" for key in negatives) or
            (cases["original-mul"]["baseline_exit_code"], cases["original-mul"]["patched_exit_code"]) != (1, 0) or
            cases["without-checks"]["exit_code"] != 1 or len(commands) != len(receipt["commands"]) or
            {name: item["exit_code"] for name, item in commands.items()} != expected_codes or
            commands["original-mul"]["command"] != extraction["command"] or
            "-checks" in commands["without-checks"]["command"] or "-checks" not in commands["square-control"]["command"]):
        raise RuntimeError("dense-mul regression matrix is incomplete")


def check_horner_match_variant(variant, receipt, runtime, runtime_head, linkage):
    """Validate the checked context matcher variant and all guard controls."""
    directory = "tooling/aeneas-horner-match/"
    patch = directory + "ended-shared-scalar.patch"
    source = "src/interp/InterpMatchCtxs.ml"
    input_path = "extraction/portable-horner/arithmetic.llbc"
    outputs = {"extraction/portable-horner/Arithmetic/" + name for name in
               ("Types.lean", "Funs.lean", "TypesExternal_Template.lean", "FunsExternal_Template.lean")}
    controls = {directory + name for name in ("run.py", "guards/dune", "guards/horner_match_guards.ml",
                "tests/Cargo.toml", "tests/Cargo.lock", "tests/src/lib.rs")}
    if (receipt["status"] != "passed" or receipt["variant_id"] != variant["id"] or
            receipt["native_source_changed"] is not False or receipt["new_native_coverage_credit_from_tests"] != 0 or
            variant["receipt"] != directory + "receipt.json" or variant["base_commit"] != runtime_head or
            receipt["base_aeneas_commit"] != runtime_head or receipt["charon_commit"] != linkage["charon_commit"] or
            variant["mandatory_checks"] is not True or variant["patch"] != patch or receipt["patch"] != patch or
            receipt["patch_sha256"] != variant["patch_sha256"] or sha(ROOT / patch) != variant["patch_sha256"] or
            set(receipt["modified_sources"]) != {source} or receipt["base_sources"] != {source: sha(runtime / source)} or
            re.findall(r"(?m)^diff --git a/(\S+) b/(\S+)$", (ROOT / patch).read_text()) != [(source, source)]):
        raise RuntimeError("Horner matcher lost pinned provenance")
    extraction = receipt["extraction"]
    if (extraction["input"] != input_path or sha(ROOT / input_path) != extraction["input_sha256"] or
            extraction["exit_code"] != 0 or set(extraction["required_flags"]) != {"-checks", "-sequential"} or
            not set(extraction["required_flags"]) <= set(extraction["command"]) or
            len(extraction["generated"]) != len(outputs) or
            {item["path"] for item in extraction["generated"]} != outputs or
            any(sha(ROOT / item["path"]) != item["sha256"] for item in extraction["generated"])):
        raise RuntimeError("Horner matcher lost checked original extraction")
    if (set(receipt["regression_sources"]) != controls or
            any(sha(ROOT / path) != digest for path, digest in receipt["regression_sources"].items())):
        raise RuntimeError("Horner matcher regression sources changed")
    positives = {"split-then-zip", "zip-without-split", "original-horner", "same-scalar-equivalence", "same-scalar-mapping"}
    negatives = {"without-checks", "distinct-child-payload", "loan-child", "nonempty-child-mismatch",
                 "nonscalar-metadata", "same-scalar-unchecked", "unequal-symbolic-id"}
    codes = {"charon-fixture": 0, "fixture-baseline": 1, "fixture-checked": 0, "fixture-without-checks": 1,
             "original-baseline": 1, "original-horner": 0, "context-matcher-guards": 0}
    cases = {item["case"]: item for item in receipt["regressions"]}
    commands = {item["name"]: item for item in receipt["commands"]}
    if (set(cases) != positives | negatives or len(cases) != len(receipt["regressions"]) or
            any(cases[key]["status"] != "passed" for key in positives) or
            any(cases[key]["status"] != "expected_rejection_confirmed" for key in negatives) or
            any((cases[key]["baseline_exit_code"], cases[key]["patched_exit_code"]) != (1, 0)
                for key in ("split-then-zip", "original-horner")) or cases["without-checks"]["exit_code"] != 1 or
            len(commands) != len(receipt["commands"]) or
            {name: item["exit_code"] for name, item in commands.items()} != codes or
            commands["original-horner"]["command"] != extraction["command"] or
            "-checks" not in commands["fixture-checked"]["command"] or
            "-checks" in commands["fixture-without-checks"]["command"]):
        raise RuntimeError("Horner matcher regression matrix is incomplete")


def check_certificate_match_variant(variant, receipt, runtime, runtime_head, linkage):
    directory = "tooling/aeneas-ended-projector/"
    source = "src/interp/InterpMatchCtxs.ml"
    patch = directory + "ended-projector-leaf.patch"
    extraction_dir = "extraction/degree-certificate/"
    if (receipt["status"] != "passed" or receipt["variant_id"] != variant["id"] or
            receipt["native_source_changed"] is not False or receipt["new_native_coverage_credit_from_tests"] != 0 or
            variant["receipt"] != directory + "receipt.json" or variant["base_commit"] != runtime_head or
            receipt["base_aeneas_commit"] != runtime_head or receipt["charon_commit"] != linkage["charon_commit"] or
            variant["mandatory_checks"] is not True or variant["patch"] != patch or receipt["patch"] != patch or
            receipt["patch_sha256"] != variant["patch_sha256"] or sha(ROOT / patch) != variant["patch_sha256"] or
            set(receipt["modified_sources"]) != {source} or receipt["base_sources"] != {source: sha(runtime / source)} or
            re.findall(r"(?m)^--- a/(\S+)\n\+\+\+ b/(\S+)$", (ROOT / patch).read_text()) != [(source, source)]):
        raise RuntimeError("Certificate matcher lost pinned provenance")
    extraction = receipt["extraction"]
    outputs = {extraction_dir + "Arithmetic/" + name for name in
               ("Funs.lean", "Types.lean", "FunsExternal_Template.lean")}
    flags = {"-checks", "-sequential"}
    if (extraction["input"] != extraction_dir + "arithmetic.llbc" or
            sha(ROOT / extraction["input"]) != extraction["input_sha256"] or extraction["exit_code"] != 0 or
            set(extraction["required_flags"]) != flags or not flags <= set(extraction["command"]) or
            len(extraction["generated"]) != len(outputs) or {item["path"] for item in extraction["generated"]} != outputs or
            any(sha(ROOT / item["path"]) != item["sha256"] for item in extraction["generated"])):
        raise RuntimeError("Certificate matcher lost checked original extraction")
    controls = {directory + name for name in ("guards/dune", "guards/ended_projector_guards.ml",
                                               "guard-controls.log", "unchecked.log")}
    rejection = receipt["pinned_rejection"]
    if (set(receipt["regression_sources"]) != controls or
            any(sha(ROOT / path) != digest for path, digest in receipt["regression_sources"].items()) or
            rejection["log"] != extraction_dir + "aeneas-pinned-rejection.log" or rejection["exit_code"] != 1 or
            sha(ROOT / rejection["log"]) != rejection["sha256"]):
        raise RuntimeError("Certificate matcher rejection evidence changed")
    cases = {item["case"]: item["status"] for item in receipt["regressions"]}
    commands = {item["name"]: item for item in receipt["commands"]}
    if (len(cases) != len(receipt["regressions"]) or cases != {
            **dict.fromkeys(("identical-mapping", "identical-equivalence"), "passed"),
            **dict.fromkeys(("different-ended-id", "different-type", "identical-consumed-child",
                             "identical-borrow-child", "identical-marked-projector", "unchecked-identical"),
                            "expected_rejection_confirmed"),
            } or len(commands) != len(receipt["commands"]) or
            {name: item["exit_code"] for name, item in commands.items()} != {
                "original-certificate": 0, "without-checks": 1, "ended-projector-guards": 0} or
            commands["original-certificate"]["command"] != extraction["command"] or
            "-checks" in commands["without-checks"]["command"]):
        raise RuntimeError("Certificate matcher regression matrix is incomplete")


def check_quartic_array_retry_variant(variant, receipt, runtime, runtime_head, linkage):
    directory = "extraction/quartic/"
    patch = directory + "translator/checked-array-loan-retry.patch"
    sources = {"src/interp/" + stem + suffix
               for stem in ("InterpJoin", "InterpMatchCtxs") for suffix in (".ml", ".mli")}
    if (variant["receipt"] != directory + "receipt.json" or variant["base_commit"] != runtime_head or
            variant["mandatory_checks"] is not True or variant["patch"] != patch or
            receipt["aeneas_commit"] != runtime_head or receipt["charon_commit"] != linkage["charon_commit"] or
            receipt["source_commit"] != linkage["source_commit"] or
            receipt["candidate_variant"] != variant["id"] or
            receipt["base_extension"] != "checked-ended-projector-leaf-v1" or
            receipt["status"] != "checked_original_closure_extracted" or
            receipt["native_source_edited"] is not False or receipt["native_body_proof_credit"] != 0 or
            receipt["patch_sha256"] != variant["patch_sha256"] or
            sha(ROOT / patch) != variant["patch_sha256"] or set(receipt["modified_sources"]) != sources or
            receipt["base_sources"] != {name: sha(runtime / name) for name in sources} or
            set(re.findall(r"(?m)^--- a/(\S+)\n\+\+\+ b/(\S+)$", (ROOT / patch).read_text()))
                != {(name, name) for name in sources}):
        raise RuntimeError("quartic array retry lost checked translator provenance")
    commands = {row["name"]: row for row in receipt["commands"]}
    codes = {"charon": 0, "candidate-build": 0, "narrow": 0, "replay": 0, "unchecked": 1, "pinned": 1,
             "cubic-control": 0, "certificate-control": 0, "guard-controls": 0}
    expected_controls = {"end-left-shared", "end-right-shared", "unchecked", "original-mode",
                         "non-array", "non-scalar-elements", "mismatched-payload-type", "payload-active-loan"}
    if (len(commands) != len(receipt["commands"]) or
            {name: row["exit_code"] for name, row in commands.items()} != codes or
            any(not {"-checks", "-sequential"} <= set(commands[name]["command"])
                for name in ("narrow", "replay", "pinned", "cubic-control", "certificate-control")) or
            "-checks" in commands["unchecked"]["command"] or
            len(receipt["guard_controls"]) != len(expected_controls) or
            set(receipt["guard_controls"]) != expected_controls or
            any(receipt[name] != 3 for name in ("replayed_outputs_byte_identical",
                "unrelated_cubic_control_byte_identical", "unrelated_certificate_control_byte_identical"))):
        raise RuntimeError("quartic array retry regression matrix changed")
    original = directory + "arithmetic.llbc"
    input_paths = dict.fromkeys(("narrow", "replay", "pinned", "unchecked"), original)
    input_paths.update({"cubic-control": "extraction/cubic/arithmetic.llbc",
                        "certificate-control": "extraction/degree-certificate/arithmetic.llbc"})
    logs = {"narrow": "translator/narrow.log", "replay": "aeneas.log", "pinned": "pinned.log",
            "unchecked": "unchecked.log", "cubic-control": "translator/cubic-control.log",
            "certificate-control": "translator/certificate-control.log"}
    destination = [arg.removeprefix("--dest-file=") for arg in commands["charon"]["command"]
                   if arg.startswith("--dest-file=")]
    checked_binary = commands["replay"]["command"][0]
    linked = {entry["path"]: entry["sha256"] for entry in linkage["extractions"]}
    if len(destination) != 1 or Path(destination[0]).name != "arithmetic.llbc":
        raise RuntimeError("quartic extraction command lost its LLBC destination")
    for name, path in input_paths.items():
        command = commands[name]
        input_arg = Path(command["command"][-1])
        expected = Path(path)
        if (command["input_sha256"] != linked[path] or linked[path] != sha(ROOT / path) or
                (str(input_arg) != destination[0] if path == original else
                 input_arg.parts[-len(expected.parts):] != expected.parts) or
                command["log_sha256"] != receipt["files_sha256"][directory + logs[name]] or
                command["log_sha256"] != sha(ROOT / directory / logs[name]) or
                (name != "pinned" and command["command"][0] != checked_binary)):
            raise RuntimeError("quartic replay command lost its input or log linkage: " + name)
    outputs = {"replay": directory, "cubic-control": "extraction/cubic/",
               "certificate-control": "extraction/degree-certificate/"}
    if receipt["replay_output_sha256"] != {
            name: {file: sha(ROOT / path / "Arithmetic" / file)
                   for file in ("Funs.lean", "Types.lean", "FunsExternal_Template.lean")}
            for name, path in outputs.items()}:
        raise RuntimeError("quartic replay output fingerprints changed")
    with tempfile.TemporaryDirectory(prefix="quartic-checked-translator-") as temporary:
        work = Path(temporary)
        for name in sources:
            (work / name).parent.mkdir(parents=True, exist_ok=True)
            (work / name).write_bytes((runtime / name).read_bytes())
        applied = subprocess.run(["git", "apply", str(ROOT / patch)], cwd=work,
                                 capture_output=True, timeout=30)
        if applied.returncode or receipt["modified_sources"] != {name: sha(work / name) for name in sources}:
            raise RuntimeError("quartic retry patched translator sources changed")


def check_newton_slice_retry_variant(variant, receipt, runtime, runtime_head, linkage):
    directory = "extraction/deg34-guard/"
    patch = directory + "translator/checked-nested-slice-loan-retry.patch"
    delta = directory + "translator/nested-slice-loan-retry-delta.patch"
    base = next((entry for entry in linkage["reviewed_translator_variants"]
                 if entry["id"] == "checked-fixedpoint-scalar-array-loan-retry-v1"), None)
    if (base is None or variant["receipt"] != directory + "receipt.json" or variant["patch"] != patch or
            variant["base_commit"] != runtime_head or variant["mandatory_checks"] is not True or
            receipt["candidate_variant"] != variant["id"] or receipt["extension_of"] != base["id"] or
            receipt["aeneas_commit"] != runtime_head or receipt["charon_commit"] != linkage["charon_commit"] or
            receipt["source_commit"] != linkage["source_commit"] or
            receipt["native_body_proof_credit"] != 0 or receipt["native_source_edited"] is not False or
            receipt["full_patch_sha256"] != variant["patch_sha256"] or
            sha(ROOT / patch) != variant["patch_sha256"] or sha(ROOT / delta) != receipt["delta_patch_sha256"] or
            receipt["delta_modified_source"] != "src/interp/InterpMatchCtxs.ml" or
            sha(ROOT / base["patch"]) != base["patch_sha256"]):
        raise RuntimeError("Newton guard slice retry lost checked variant provenance")
    checks = {entry["name"]: entry for entry in receipt["checks"]}
    codes = {"charon": 0, "build": 0, "Arithmetic": 1, "slice-retry": 0, "replay": 0, "pinned": 1,
             "unchecked": 1, "quartic-control": 0, "normalize-control": 0, "guard-controls": 0}
    if len(checks) != len(receipt["checks"]) or {name: entry["exit_code"] for name, entry in checks.items()} != codes:
        raise RuntimeError("Newton guard slice retry regression matrix changed")
    destinations = [arg.removeprefix("--dest-file=") for arg in checks["charon"]["command"]
                    if arg.startswith("--dest-file=")]
    charon = checks["charon"]["command"]
    if (charon[1:4] != ["cargo", "--preset=aeneas", "--sysroot=default"] or
            Path(charon[0]).parts[-4:] != ("tooling", "charon", "bin", "charon") or
            charon[5:7] != ["--start-from=bulksketch::decode::deg34::guard", "--"] or
            not charon[7].startswith("--manifest-path=") or
            charon[8:] != ["-p", "bulksketch", "--lib", "--locked", "--target", "x86_64-apple-darwin"]):
        raise RuntimeError("Newton guard recorded Charon selector or tool role changed")
    manifest = Path(charon[7].removeprefix("--manifest-path="))
    captured = manifest.parent.parent / "bulksketch-proof-evidence-20261109-closed-leaf/deg34-guard/arithmetic.llbc"
    if destinations != [str(captured)]:
        raise RuntimeError("Newton guard recorded Charon destination changed")
    slice_binary = checks["slice-retry"]["command"][0]
    pinned_binary = checks["pinned"]["command"][0]
    array_binary = checks["Arithmetic"]["command"][0]
    if (Path(slice_binary).parts[-5:] != ("deg34-slice-loan-retry", "src", "_build", "default", "main.exe") or
            Path(pinned_binary).parts[-6:] != ("tooling", "aeneas", "src", "_build", "default", "main.exe") or
            Path(array_binary).parts[-5:] != ("quartic-array-loan-retry", "src", "_build", "default", "main.exe") or
            any(checks[name]["command"][0] != slice_binary for name in
                ("replay", "unchecked", "quartic-control", "normalize-control")) or
            receipt["tool_binary_sha256"] != {
                charon[0]: "913e7969d1a0296038d115bcf1af47f8c0c6702266cc7a78a02a2b4ad7a0dfbe",
                slice_binary: "656ad7c927561d91b8d1e752c829abd557ed32808dec1a776b3796fed525f90b",
                pinned_binary: "91f5a2776a79e2923517a2c4807c9fc017e79f185ae490502247f16e2941e330",
                array_binary: "99c2c9f4db95a14cc0178b7373c247419e6ac6a424d8f7e5eda3e063ddcaf3d0"}):
        raise RuntimeError("Newton guard recorded translator binaries changed")
    original = directory + "arithmetic.llbc"
    paths = dict.fromkeys(("Arithmetic", "slice-retry", "replay", "pinned", "unchecked"), original)
    paths.update({"quartic-control": "extraction/quartic/arithmetic.llbc",
                  "normalize-control": "extraction/deg34-normalize/arithmetic.llbc"})
    linked = {entry["path"]: entry["sha256"] for entry in linkage["extractions"]}
    for name, path in paths.items():
        entry = checks[name]
        arg = Path(entry["command"][-1])
        expected = Path(path)
        if (len(destinations) != 1 or
                (str(arg) != destinations[0] if path == original else arg.parts[-len(expected.parts):] != expected.parts) or
                entry["input_sha256"] != linked[path] or linked[path] != sha(ROOT / path) or
                "-sequential" not in entry["command"] or ("-checks" in entry["command"]) != (name != "unchecked")):
            raise RuntimeError("Newton guard retry command lost its LLBC input: " + name)
    base_receipt = json.loads((ROOT / base["receipt"]).read_text())
    files = base_receipt["base_sources"]
    source = receipt["delta_modified_source"]
    if files != {name: sha(runtime / name) for name in files}:
        raise RuntimeError("Newton guard retry base sources changed")
    with tempfile.TemporaryDirectory(prefix="checked-newton-slice-retry-") as directory_path:
        temp = Path(directory_path)
        combined = temp / "combined"
        incremental = temp / "incremental"
        for tree in (combined, incremental):
            for name in files:
                path = tree / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes((runtime / name).read_bytes())
        for tree, relative in ((combined, patch), (incremental, base["patch"])):
            applied = subprocess.run(["git", "apply", str(ROOT / relative)], cwd=tree,
                                     capture_output=True, timeout=30)
            if applied.returncode:
                raise RuntimeError("Newton guard retry patch no longer applies: " + relative)
        if sha(incremental / source) != receipt["delta_base_sha256"]:
            raise RuntimeError("Newton guard retry delta base differs")
        applied = subprocess.run(["git", "apply", str(ROOT / delta)], cwd=incremental,
                                 capture_output=True, timeout=30)
        if (applied.returncode or sha(incremental / source) != receipt["delta_modified_sha256"] or
                any(sha(combined / name) != sha(incremental / name) for name in files)):
            raise RuntimeError("Newton guard full and incremental patches differ")


def check_bm_locator_variant(variant, receipt, runtime, runtime_head, linkage):
    directory = "extraction/bm-locator/"
    patch = directory + "checked-bm-locator.patch"
    names = {"src/Config.ml", "src/PrePasses.ml", "src/interp/InterpMatchCtxs.ml",
             "src/interp/InterpStatements.ml", "src/symbolic/SymbolicToPureExpressions.ml"}
    if (variant["receipt"] != directory + "receipt.json" or variant["patch"] != patch or
            variant["base_commit"] != runtime_head or variant["mandatory_checks"] is not True or
            receipt["variant_id"] != variant["id"] or receipt["aeneas_commit"] != runtime_head or
            receipt["charon_commit"] != linkage["charon_commit"] or receipt["source_commit"] != linkage["source_commit"] or
            receipt["native_body_proof_credit"] != 0 or receipt["native_source_edited"] is not False or
            receipt["variant_patch"] != patch or receipt["variant_patch_sha256"] != variant["patch_sha256"] or
            sha(ROOT / patch) != variant["patch_sha256"] or
            receipt["base_sources"] != {name: sha(runtime / name) for name in names} or
            set(receipt["modified_sources"]) != names):
        raise RuntimeError("BM locator variant lost its checked source provenance")
    checked = receipt["checked_extraction"]
    replay = receipt["replay"]
    controls = receipt["controls"]
    flags = {"-checks", "-sequential"}
    env = {"BULKSKETCH_BM_LOCATOR": "1"}
    original = directory + "arithmetic.llbc"
    linked = {item["path"]: item["sha256"] for item in linkage["extractions"]}
    binary = checked["command"][0]
    source_path = Path(checked["command"][-1])
    guard = json.loads((ROOT / "extraction/deg34-guard/receipt.json").read_text())
    capture = next(item["command"] for item in guard["checks"] if item["name"] == "charon")
    manifest = Path(capture[7].removeprefix("--manifest-path="))
    recorded_input = manifest.parent / "verification/lean" / original
    if (checked["input"] != original or checked["input_sha256"] != linked[original] or
            linked[original] != sha(ROOT / original) or
            source_path != recorded_input or
            Path(binary).parts[-5:] != ("aeneas-bm-locator-v1", "src", "_build", "default", "main.exe") or
            receipt["tool_binary_sha256"] != {
                "aeneas": "87cb462ec8314b62964f1e35daca6cfaaa5ba4bd3e7c29f1c02a3745d39daceb",
                "aeneas_pinned": "91f5a2776a79e2923517a2c4807c9fc017e79f185ae490502247f16e2941e330"} or
            any(item["exit_code"] != 0 or item["environment"] != env or
                not flags <= set(item["command"]) or item["command"][0] != binary or
                item["command"][1:3] != ["-backend", "lean"] or
                Path(item["command"][-1]) != source_path for item in (checked, replay)) or
            replay["exact_generated_artifacts"] != 3 or receipt["portable_xor_exact_artifacts"] != 3 or
            set(controls) != {"disabled", "unchecked", "portable-xor", "portable-xor-baseline"}):
        raise RuntimeError("BM locator checked replay linkage changed")
    xor_input = source_path.parent.parent / "portable-xor/arithmetic.llbc"
    xor_path = "extraction/portable-xor/arithmetic.llbc"
    if linked[xor_path] != sha(ROOT / xor_path):
        raise RuntimeError("BM locator compatibility LLBC changed")
    for name, enabled, with_checks, code in (("disabled", False, True, 1), ("unchecked", True, False, 1),
                                             ("portable-xor", True, True, 0), ("portable-xor-baseline", False, True, 0)):
        row = controls[name]
        command = row["command"]
        if (row["name"] != name or row["exit_code"] != code or row["environment"] != (env if enabled else {}) or
                command[1:3] != ["-backend", "lean"] or
                "-sequential" not in command or ("-checks" in command) != with_checks or
                (command[0] != binary if name != "portable-xor-baseline" else
                    Path(command[0]).parts[-6:] != ("tooling", "aeneas", "src", "_build", "default", "main.exe")) or
                Path(command[-1]) != (source_path if code else xor_input) or
                sha(ROOT / directory / (name + ".log")) != row["log_sha256"]):
            raise RuntimeError("BM locator control linkage changed: " + name)
    with tempfile.TemporaryDirectory(prefix="checked-bm-locator-") as temporary:
        work = Path(temporary)
        for name in names:
            path = work / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes((runtime / name).read_bytes())
        applied = subprocess.run(["git", "apply", str(ROOT / patch)], cwd=work,
                                 capture_output=True, timeout=30)
        if applied.returncode or receipt["modified_sources"] != {name: sha(work / name) for name in names}:
            raise RuntimeError("BM locator patched sources changed")


def check_dense_reducer_variant(variant, receipt, runtime, runtime_head, linkage):
    files = {
        "checked-dense-reducer-option-v1": (
            "extraction/dense-reducer-table/", "checked-dense-reducer-option.patch",
            {"src/interp/InterpMatchCtxs.ml"}),
        "checked-dense-reducer-square-v1": (
            "extraction/dense-reducer-square/", "checked-dense-reducer-square.patch",
            {"src/interp/InterpMatchCtxs.ml", "src/interp/InterpExpansion.ml",
             "src/symbolic/SymbolicToPureExpressions.ml"}),
        "checked-dense-div-rem-v1": (
            "extraction/dense-div-rem/", "checked-dense-div-rem.patch",
            {"src/Translate.ml", "src/interp/InterpBorrows.ml", "src/interp/InterpBorrows.mli",
             "src/interp/InterpBorrowsCore.ml", "src/interp/InterpExpansion.ml", "src/interp/InterpLoops.ml",
             "src/interp/InterpMatchCtxs.ml", "src/interp/InterpStatements.ml",
             "src/symbolic/SymbolicToPureCore.ml", "src/symbolic/SymbolicToPureExpressions.ml"}),
        "checked-candidates-nested-return-v1": (
            "extraction/candidates/", "checked-candidates-nested-return.patch", {"src/PrePasses.ml"}),
        "checked-native-deflate-loan-retry-v1": (
            "extraction/native-deflate/", "checked-native-deflate-loan-retry.patch",
            {"src/interp/InterpMatchCtxs.ml"}),
        "checked-affine-outer-continue-v1": (
            "extraction/affine-enumerate/", "checked-affine-outer-continue.patch", {"src/PrePasses.ml"}),
        "checked-affine-multiple-zip-ends-v1": (
            "extraction/affine-multiple/", "checked-affine-multiple-zip-ends.patch",
            {"src/interp/InterpStatements.ml", "src/interp/InterpBorrows.ml",
             "src/interp/InterpBorrows.mli", "src/interp/InterpBorrowsCore.ml", "src/interp/InterpAbs.ml"}),
    }
    directory, name, sources = files[variant["id"]]
    patch = directory + name
    if (variant["receipt"] != directory + "receipt.json" or variant["patch"] != patch or
            variant["base_commit"] != runtime_head or variant["mandatory_checks"] is not True or
            receipt["variant_id"] != variant["id"] or receipt["aeneas_commit"] != runtime_head or
            receipt["charon_commit"] != linkage["charon_commit"] or receipt["source_commit"] != linkage["source_commit"] or
            receipt["native_source_edited"] is not False or receipt["variant_patch"] != patch or
            receipt["variant_patch_sha256"] != variant["patch_sha256"] or
            sha(ROOT / patch) != variant["patch_sha256"] or
            receipt["base_sources"] != {source: sha(runtime / source) for source in sources} or
            set(receipt["modified_sources"]) != sources):
        raise RuntimeError("Dense reducer variant lost its checked source provenance")
    with tempfile.TemporaryDirectory(prefix="checked-dense-reducer-") as temporary:
        work = Path(temporary)
        for source in sources:
            copied = work / source
            copied.parent.mkdir(parents=True, exist_ok=True)
            copied.write_bytes((runtime / source).read_bytes())
        applied = subprocess.run(["git", "apply", str(ROOT / patch)], cwd=work,
                                 capture_output=True, timeout=30)
        if applied.returncode or receipt["modified_sources"] != {source: sha(work / source) for source in sources}:
            raise RuntimeError("Dense reducer patched sources differ")


def check_degree_probe_extension(extension, receipt, variants, runtime_head, linkage):
    directory = "extraction/degree-probe/"
    variant = next((entry for entry in variants if entry["id"] == "checked-fixedpoint-nested-scalar-slice-retry-v1"), None)
    if (variant is None or extension["variant"] != variant["id"] or
            extension["receipt"] != directory + "receipt.json" or receipt["candidate_variant"] != variant["id"] or
            receipt["full_patch_sha256"] != variant["patch_sha256"] or receipt["aeneas_commit"] != runtime_head or
            receipt["charon_commit"] != linkage["charon_commit"] or receipt["source_commit"] != linkage["source_commit"] or
            receipt["native_body_proof_credit"] != 0 or receipt["native_source_edited"] is not False or
            receipt["transparent_application_bodies"] is not True or receipt["guard_declarations_byte_identical"] != 13):
        raise RuntimeError("DegreeProbe lost the reviewed nested-slice extension")
    guard = json.loads((ROOT / variant["receipt"]).read_text())
    parent_checks = {item["name"]: item for item in guard["checks"]}
    commands = {row["name"]: row for row in receipt["checks"]}
    codes = {"charon": 0, "Arithmetic": 0, "replay": 0, "pinned": 1, "unchecked": 1}
    if (len(commands) != len(receipt["checks"]) or
            {name: row["exit_code"] for name, row in commands.items()} != codes or
            receipt["replayed_files_byte_identical"] != 3 or
            receipt["tool_binary_sha256"] != guard["tool_binary_sha256"] or
            receipt["guard_projection_receipt_sha256"] != sha(ROOT / variant["receipt"])):
        raise RuntimeError("DegreeProbe replay matrix changed")
    charon = commands["charon"]["command"]
    manifest = Path(charon[7].removeprefix("--manifest-path="))
    captured = manifest.parent.parent / "bulksketch-proof-evidence-20261109-closed-leaf/degree-probe-run/arithmetic.llbc"
    if (charon[0] != parent_checks["charon"]["command"][0] or
            charon[1:4] != ["cargo", "--preset=aeneas", "--sysroot=default"] or
            charon[4:7] != ["--dest-file=" + str(captured), "--start-from=bulksketch::decode::degree_probe", "--"] or
            charon[7] != parent_checks["charon"]["command"][7] or
            charon[8:] != ["-p", "bulksketch", "--lib", "--locked", "--target", "x86_64-apple-darwin"]):
        raise RuntimeError("DegreeProbe recorded Charon command changed")
    path = directory + "arithmetic.llbc"
    linked = {row["path"]: row["sha256"] for row in linkage["extractions"]}
    if linked[path] != sha(ROOT / path):
        raise RuntimeError("DegreeProbe checked input fingerprint changed")
    for name, log in (("Arithmetic", "aeneas.log"), ("replay", "aeneas.log"),
                      ("pinned", "pinned.log"), ("unchecked", "unchecked.log")):
        row = commands[name]
        command = row["command"]
        parent = name if name == "pinned" else "replay"
        if (command[0] != parent_checks[parent]["command"][0] or Path(command[-1]) != captured or
                command[1:3] != ["-backend", "lean"] or
                "-sequential" not in command or ("-checks" in command) != (name != "unchecked") or
                row["input_sha256"] != linked[path] or
                (name != "Arithmetic" and row["log_sha256"] != sha(ROOT / directory / log))):
            raise RuntimeError("DegreeProbe replay command lost its input or log linkage: " + name)


def check_pclmul_horner_extension(extension, receipt, variants, runtime_head, linkage):
    """Bind the second original Horner extraction to the reviewed matcher."""
    variant = next((entry for entry in variants if entry["id"] == "checked-ended-shared-scalar-v1"), None)
    directory = "extraction/pclmul-horner/"
    extraction = receipt["checked_extraction"]
    outputs = {directory + "Arithmetic/" + name for name in
               ("Funs.lean", "Types.lean", "FunsExternal_Template.lean", "TypesExternal_Template.lean")}
    if (variant is None or extension["variant"] != variant["id"] or
            extension["receipt"] != directory + "receipt.json" or receipt["aeneas_variant"] != variant["id"] or
            receipt["variant_patch"] != variant["patch"] or receipt["variant_patch_sha256"] != variant["patch_sha256"] or
            receipt["status"] != "generated" or receipt["native_source_edited"] is not False or
            receipt["target"] != "x86_64-apple-darwin" or receipt["aeneas_commit"] != runtime_head or
            receipt["charon_commit"] != linkage["charon_commit"] or receipt["source_commit"] != linkage["source_commit"] or
            extraction["input"] != directory + "arithmetic.llbc" or
            sha(ROOT / extraction["input"]) != extraction["input_sha256"] or
            extraction["input_sha256"] != receipt["llbc_sha256"] or extraction["exit_code"] != 0 or
            set(extraction["required_flags"]) != {"-checks", "-sequential"} or
            not set(extraction["required_flags"]) <= set(extraction["command"]) or
            len(extraction["generated"]) != len(outputs) or {item["path"] for item in extraction["generated"]} != outputs or
            any(sha(ROOT / item["path"]) != item["sha256"] for item in extraction["generated"])):
        raise RuntimeError("PCLMUL Horner lost checked extraction provenance")
    rejected = receipt["rejections"]
    replay = receipt["replay"]
    if (set(rejected) != {"pinned", "unchecked"} or
            any(entry["exit_code"] != 1 for entry in rejected.values()) or
            "-checks" not in rejected["pinned"]["command"] or "-checks" in rejected["unchecked"]["command"] or
            replay["exit_code"] != 0 or replay["exact_generated_artifacts"] != len(outputs) or
            not set(extraction["required_flags"]) <= set(replay["command"])):
        raise RuntimeError("PCLMUL Horner checked replay controls changed")


def check_stateful_linkage(stateful, receipt, aeneas_projections):
    """Bind checked LLBC program names to their source IDs, outside Aeneas credit."""
    if (receipt["compiled_projection"] != stateful["program_file"] or
            receipt["projection_sha256"] != stateful["projection_sha256"] or
            receipt["llbc_sha256"] != stateful["llbc_sha256"] or
            receipt["source_sha256"] != stateful["source_sha256"] or
            receipt["programs"] != stateful["programs"] or receipt["native_body_proof_credit"] != 0 or
            any(item["bridge_copy"] == stateful["program_file"] for item in aeneas_projections)):
        raise RuntimeError("stateful LLBC projection lost its source or entered Aeneas body coverage")


def main():
    scope = json.loads((ROOT / "scope.json").read_text())
    source = (ROOT / scope["source_repository"]).resolve()
    head = subprocess.check_output(["git", "-C", str(source), "rev-parse", "HEAD"], text=True).strip()
    inventory = json.loads((ROOT / "audit/source-inventory.json").read_text())
    for file in inventory["files"]:
        if sha(source / file["path"]) != file["sha256"]:
            raise RuntimeError("native source body drift")
    for path, expected in scope["source_build_inputs_sha256"].items():
        if sha(source / path) != expected:
            raise RuntimeError("native build input drift: " + path)
    frozen = json.loads((AUDIT / "frozen-inputs.json").read_text())
    for path, expected in frozen["files"].items():
        if sha(ROOT / path) != expected:
            raise RuntimeError("frozen bridge/source/model input drift: " + path)
    linkage = json.loads((BRIDGE / "source-linkage.json").read_text())
    runtime = ROOT / "tooling/aeneas"
    runtime_head = subprocess.check_output(["git", "-C", str(runtime), "rev-parse", "HEAD"], text=True).strip()
    if runtime_head != linkage["aeneas_commit"] or subprocess.check_output(
            ["git", "-C", str(runtime), "status", "--porcelain", "--untracked-files=no"], text=True).strip():
        raise RuntimeError("Aeneas runtime differs from its clean reviewed source pin")
    for item in linkage["extractions"]:
        if sha(ROOT / item["path"]) != item["sha256"] or \
                json.loads((ROOT / item["path"]).read_text())["has_errors"] is not False:
            raise RuntimeError("incomplete or stale native extraction")
    for item in linkage["native_generated_copies"]:
        if (ROOT / item["generated"]).read_bytes() != (ROOT / item["bridge_copy"]).read_bytes():
            raise RuntimeError("application-generated body was edited")
        if sha(ROOT / item["bridge_copy"]) != item["sha256"]:
            raise RuntimeError("generated-body linkage hash is stale")
    registry = json.loads((BRIDGE / "obligations.json").read_text())
    coverage = json.loads((ROOT / "audit/coverage.json").read_text())
    if {item["id"] for item in coverage["items"]} != {item["id"] for item in inventory["items"]}:
        raise RuntimeError("native obligation disappeared from coverage denominator")
    records = []
    variants = linkage.get("reviewed_translator_variants", [])
    for variant in variants:
        receipt = json.loads((ROOT / variant["receipt"]).read_text())
        if variant["id"] == "checked-shared-expansion-owner-v1":
            check_dense_prefix_variant(variant, receipt, runtime, runtime_head, linkage)
            result, _ = run("checked-dense-prefix-patch-applies", ["git", "apply", "--check",
                            str(ROOT / variant["patch"])], timeout=30, cwd=runtime)
            records.append(result)
            continue
        if variant["id"] == "checked-shared-loop-erasure-v1":
            check_dense_mul_variant(variant, receipt, runtime, runtime_head, linkage)
            result, _ = run("checked-dense-mul-patch-applies", ["git", "apply", "--check",
                            str(ROOT / variant["patch"])], timeout=30, cwd=runtime)
            records.append(result)
            continue
        if variant["id"] == "checked-ended-shared-scalar-v1":
            check_horner_match_variant(variant, receipt, runtime, runtime_head, linkage)
            result, _ = run("checked-horner-matcher-patch-applies", ["git", "apply", "--check",
                            str(ROOT / variant["patch"])], timeout=30, cwd=runtime)
            records.append(result)
            continue
        if variant["id"] == "checked-ended-projector-leaf-v1":
            check_certificate_match_variant(variant, receipt, runtime, runtime_head, linkage)
            result, _ = run("checked-certificate-matcher-patch-applies", ["git", "apply", "--check",
                            str(ROOT / variant["patch"])], timeout=30, cwd=runtime)
            records.append(result)
            continue
        if variant["id"] == "checked-fixedpoint-scalar-array-loan-retry-v1":
            check_quartic_array_retry_variant(variant, receipt, runtime, runtime_head, linkage)
            result, _ = run("checked-quartic-array-retry-patch-applies", ["git", "apply", "--check",
                            str(ROOT / variant["patch"])], timeout=30, cwd=runtime)
            records.append(result)
            continue
        if variant["id"] == "checked-fixedpoint-nested-scalar-slice-retry-v1":
            check_newton_slice_retry_variant(variant, receipt, runtime, runtime_head, linkage)
            result, _ = run("checked-newton-slice-retry-patch-applies", ["git", "apply", "--check",
                            str(ROOT / variant["patch"])], timeout=30, cwd=runtime)
            records.append(result)
            continue
        if variant["id"] == "checked-bm-locator-v1":
            check_bm_locator_variant(variant, receipt, runtime, runtime_head, linkage)
            result, _ = run("checked-bm-locator-patch-applies", ["git", "apply", "--check",
                            str(ROOT / variant["patch"])], timeout=30, cwd=runtime)
            records.append(result)
            continue
        if variant["id"] in {"checked-dense-reducer-option-v1", "checked-dense-reducer-square-v1",
                            "checked-dense-div-rem-v1", "checked-affine-outer-continue-v1",
                            "checked-affine-multiple-zip-ends-v1", "checked-native-deflate-loan-retry-v1",
                            "checked-candidates-nested-return-v1"}:
            check_dense_reducer_variant(variant, receipt, runtime, runtime_head, linkage)
            result, _ = run(variant["id"] + "-patch-applies", ["git", "apply", "--check",
                            str(ROOT / variant["patch"])], timeout=30, cwd=runtime)
            records.append(result)
            continue
        if variant["id"] != "checked-frozen-capture-v1":
            raise RuntimeError("unknown reviewed translator variant")
        extraction = receipt["extraction"]
        expected_sources = {"src/interp/InterpJoin.ml", "src/pure/PureUtils.ml",
                            "src/pure/PureMicroPassesLoops.ml"}
        if receipt["status"] != "passed" or receipt["base_aeneas_commit"] != runtime_head or \
                receipt["base_aeneas_commit"] != variant["base_commit"] or \
                variant["mandatory_checks"] is not True or \
                receipt["charon_commit"] != linkage["charon_commit"] or \
                receipt["patch"] != variant["patch"] or \
                receipt["patch_sha256"] != variant["patch_sha256"] or \
                sha(ROOT / variant["patch"]) != variant["patch_sha256"] or \
                set(receipt["modified_sources"]) != expected_sources or \
                set(receipt["base_sources"]) != expected_sources or \
                extraction["input"] != "extraction/canonical-arithmetic/inverse-pilot/arithmetic.llbc" or \
                len(extraction["generated"]) != 2 or \
                {item["path"] for item in extraction["generated"]} != {
                    "extraction/inverse-wrappers/Arithmetic/Types.lean",
                    "extraction/inverse-wrappers/Arithmetic/Funs.lean"} or \
                extraction["exit_code"] != 0 or "-checks" not in extraction["required_flags"] or \
                not set(extraction["required_flags"]) <= set(extraction["command"]) or \
                sha(ROOT / extraction["input"]) != extraction["input_sha256"]:
            raise RuntimeError("reviewed translator variant lost pinned provenance/checks")
        changed = re.findall(r"(?m)^diff --git a/(\S+) b/(\S+)$",
                             (ROOT / variant["patch"]).read_text())
        if {before for before, after in changed if before == after} != expected_sources or \
                len(changed) != len(expected_sources):
            raise RuntimeError("reviewed translator patch modifies unexpected files")
        if sha(runtime / "src/interp/InterpReduceCollapse.ml") != \
                receipt["unchanged_collapse_guard_source_sha256"]:
            raise RuntimeError("original nested-loan guard changed")
        for path, expected in receipt["base_sources"].items():
            if sha(runtime / path) != expected:
                raise RuntimeError("translator variant base source drift")
        for item in extraction["generated"]:
            if sha(ROOT / item["path"]) != item["sha256"]:
                raise RuntimeError("reviewed variant generated artifact drift")
        if not receipt["regressions"] or any(item["status"] not in {
                "passed", "expected_rejection_confirmed", "expected_rust_borrow_rejection_confirmed"}
                for item in receipt["regressions"]):
            raise RuntimeError("missing successful translator regression evidence")
        regressions = {item["case"]: item for item in receipt["regressions"]}
        expected_matrix = {"captured_callback": (1, 0), "aliased_shared_capture": (1, 0),
                           "captured_phantom_callback": (1, 0), "ordinary_shared_loop": (0, 0),
                           "captured_borrow_result": (1, 0), "nested_mutable_shared_capture": (1, 1),
                           "nested_shared_referent_capture": (1, 1), "captured_expandable_referent": (1, 1)}
        if len(regressions) != len(receipt["regressions"]) or \
                set(regressions) != set(expected_matrix) | {
                    "without-checks", "shared_then_mutable", "nested_shared_then_mutable"}:
            raise RuntimeError("translator regression matrix omitted a required control")
        for name, expected in expected_matrix.items():
            if (regressions[name]["baseline_exit_code"], regressions[name]["patched_exit_code"]) != expected:
                raise RuntimeError("translator positive/indirect-control outcome changed")
        if regressions["without-checks"]["exit_code"] == 0 or \
                any(regressions[name]["status"] != "expected_rust_borrow_rejection_confirmed"
                    for name in ["shared_then_mutable", "nested_shared_then_mutable"]) or \
                not any(item["name"] == "rust-value-regressions" and item["exit_code"] == 0
                        for item in receipt["commands"]):
            raise RuntimeError("translator checks/alias/value controls are incomplete")
        result, _ = run("reviewed-translator-patch-applies", ["git", "apply", "--check",
                         str(ROOT / variant["patch"])], timeout=30, cwd=runtime)
        records.append(result)
    extensions = linkage.get("reviewed_pclmul_horner_extensions", [])
    projections = linkage.get("native_generated_projections", [])
    horner_projections = [item for item in projections
                          if item["bridge_copy"] == "bridge/Arithmetic/X86PclmulHornerGenerated.lean"]
    if len(extensions) != len(horner_projections) or len(extensions) > 1:
        raise RuntimeError("PCLMUL Horner projection lacks a unique checked extraction receipt")
    for extension in extensions:
        receipt = json.loads((ROOT / extension["receipt"]).read_text())
        check_pclmul_horner_extension(extension, receipt, variants, runtime_head, linkage)
        if horner_projections[0].get("translator_variant") != extension["variant"]:
            raise RuntimeError("PCLMUL Horner projection hides its translator variant")
    probe_extensions = linkage.get("reviewed_degree_probe_extensions", [])
    probe_projections = [item for item in projections
                         if item["bridge_copy"] == "bridge/Arithmetic/DegreeProbeGenerated.lean"]
    if len(probe_extensions) != len(probe_projections) or len(probe_extensions) > 1:
        raise RuntimeError("DegreeProbe projection lacks a unique checked extension")
    for extension in probe_extensions:
        receipt = json.loads((ROOT / extension["receipt"]).read_text())
        check_degree_probe_extension(extension, receipt, variants, runtime_head, linkage)
        if probe_projections[0].get("translator_variant") != extension["variant"]:
            raise RuntimeError("DegreeProbe projection hides its translator variant")
    for projection in projections:
        result, output = run("check-projection-" + Path(projection["bridge_copy"]).stem,
            ["python3", str(ROOT / projection["checker"]), *projection.get("checker_args", [])],
            timeout=30, cwd=ROOT)
        receipt = json.loads(output)
        if receipt["compiled_projection"] != projection["bridge_copy"] or \
                receipt["raw_generated_file"] != projection["generated"] or \
                receipt["projection_file_sha256"] != projection["sha256"] or \
                receipt["raw_file_sha256"] != projection["raw_sha256"] or \
                receipt["source_declarations_retained_verbatim"] != projection["declaration_count"] or \
                receipt["shared_types_and_function_dictionary_declarations_checked"] is not True or \
                ("translator_variant" in receipt and
                 receipt["translator_variant"] != projection.get("translator_variant")):
            raise RuntimeError("declaration projection lost exact source provenance")
        records.append(result)
    for flags in ([], ["-O"]):
        suffix = "-optimized" if flags else ""
        result, output = run("check-avx-square-seed-layout" + suffix,
            ["python3", *flags, str(ROOT / "extraction/avx-square/check_seed_layout.py")],
            timeout=30, cwd=ROOT)
        layout = json.loads(output)
        if (layout["llbc_sha256"] != sha(ROOT / "extraction/avx-square/arithmetic.llbc") or
                layout["captured_raw_product"] != {"stride_bytes": 16, "alignment_bytes": 8,
                                                   "lo_bytes": 0, "hi_bytes": 8} or
                layout["rejected_layout_controls"] != ["big-endian", "narrow-word", "overlapping-raw-words"] or
                layout["rust_layout_guarantee"] is not False or
                layout["compiler_instruction_correspondence_proved"] is not False):
            raise RuntimeError("AVX square seed layout lost its exact capture and control scope")
        records.append(result)
    for diagnostic in linkage.get("diagnostic_generated_projections", []):
        result, output = run("check-diagnostic-" + Path(diagnostic["bridge_copy"]).stem,
            ["python3", str(ROOT / diagnostic["checker"])], timeout=30, cwd=ROOT)
        receipt = json.loads(output)
        if (receipt["compiled_projection"] != diagnostic["bridge_copy"] or
                receipt["projection_file_sha256"] != diagnostic["sha256"] or
                receipt["source_declarations_retained_verbatim"] != diagnostic["declaration_count"] or
                receipt["native_body_proof_credit"] != 0 or diagnostic["native_body_proof_credit"] != 0 or
                any(item["bridge_copy"] == diagnostic["bridge_copy"]
                    for item in [*linkage["native_generated_copies"], *projections])):
            raise RuntimeError("diagnostic projection lost its provenance or entered native coverage")
        records.append(result)
    stateful_projections = list(linkage.get("stateful_llbc_caller_projections", []))
    if linkage.get("stateful_llbc_projection"):
        stateful_projections.insert(0, linkage["stateful_llbc_projection"])
    stateful_by_id = {}
    for stateful in stateful_projections:
        suffix = Path(stateful["program_file"]).stem
        result, output = run("check-stateful-llbc-" + suffix,
            ["python3", str(ROOT / stateful["checker"])], timeout=30, cwd=ROOT)
        receipt = json.loads(output)
        check_stateful_linkage(stateful, receipt, [*linkage["native_generated_copies"], *projections])
        records.append(result)
        for ident in stateful["programs"]:
            if ident in stateful_by_id:
                raise RuntimeError("duplicate stateful LLBC source association")
            stateful_by_id[ident] = stateful
        for flags in ([], ["-O"]):
            result, output = run("stateful-llbc-negative-controls-" + suffix + ("-optimized" if flags else ""),
                ["python3", *flags, str(ROOT / stateful["controls"])], timeout=60, cwd=ROOT)
            rejected = [line for line in output.splitlines() if line.startswith("rejected ")]
            if len(rejected) != stateful["negative_control_count"] or len(set(rejected)) != len(rejected):
                raise RuntimeError("incomplete stateful LLBC mutation controls")
            records.append(result)
    result, _ = run("build-replay-loader", ["elan", "run", CHAIN, "lake", "build", "replay_export"],
                    timeout=120, cwd=ROOT)
    records.append(result)
    result, _ = run("build", ["elan", "run", CHAIN, "lake", "build",
                                "BulksketchBridge", "BulksketchBridge.Audit"], timeout=1200)
    records.append(result)
    result, output = run("axioms-and-challenges", ["elan", "run", CHAIN, "lake", "env",
                                                  "lean", "BulksketchBridge/Audit.lean"])
    records.append(result)
    events = []
    for line in output.splitlines():
        start = line.find('{"')
        if start >= 0: events.append(json.loads(line[start:]))
    roots = [event for event in events if event["kind"] == "theorem_axioms"]
    challenges = {(event["challenge"], event["theorem"]) for event in events
                  if event["kind"] == "challenge_match"}
    names = {event["theorem"] for event in roots}
    expected = {(item["challenge"], item["theorem"]) for item in registry["challenges"]}
    if not expected or len(expected) != frozen["challenge_count"] or challenges != expected or \
            not {item[1] for item in challenges} <= names:
        raise RuntimeError("bridge challenge omitted from axiom/export roots")
    summaries = [event for event in events if event["kind"] == "summary"]
    if len(summaries) != 1 or summaries[0]["public_theorems"] != len(roots) or \
            summaries[0]["matched_challenges"] != len(expected):
        raise RuntimeError("incomplete bridge theorem/challenge audit")
    items = {item["id"]: item for item in coverage["items"]}
    source_items = {item["id"]: item for item in inventory["items"]}
    refined = {entry["native_item_id"]: entry for entry in registry["refinements"]}
    evidence = {item["id"] for item in coverage["items"]
                if item.get("generated_body_refinement_evidence")}
    if len(refined) != len(registry["refinements"]) or evidence != set(refined):
        raise RuntimeError("unregistered or missing generated-body coverage evidence")
    if coverage["proof_progress"]["checked_generated_body_refinements_under_recorded_TCB"] != len(refined):
        raise RuntimeError("stale generated-body coverage summary")
    copies = {item["bridge_copy"] for item in linkage["native_generated_copies"]}
    copies.update(item["bridge_copy"] for item in projections)
    variant_ids = {item["id"] for item in variants}
    if len(variant_ids) != len(variants):
        raise RuntimeError("duplicate reviewed translator variant")
    for native_id, entry in refined.items():
        item = items[native_id]
        recorded = item["generated_body_refinement_evidence"]
        used_variants = {projection["translator_variant"] for projection in projections
                         if projection["bridge_copy"] in entry["generated_files"] and
                         "translator_variant" in projection}
        if used_variants != ({entry["translator_variant"]} if "translator_variant" in entry else set()) or \
                not used_variants <= variant_ids:
            raise RuntimeError("source refinement hides or lacks its translator variant")
        match = next((event for event in events if event["kind"] == "challenge_match" and
                      event["challenge"] == entry["challenge"] and event["theorem"] == entry["theorem"]), None)
        if source_items[native_id]["kind"] not in {"function", "method", "trait_default"} or \
                entry["source_linkage"] != "bridge/source-linkage.json" or \
                entry["source_line_span_sha256"] != source_items[native_id]["source_line_span_sha256"] or \
                item["source_line_span_sha256"] != source_items[native_id]["source_line_span_sha256"] or \
                match is None or entry["generated_declaration"] not in match["referenced_constants"] or \
                recorded["theorem"] != entry["theorem"] or \
                recorded["scope"] != entry["scope"] or \
                recorded["source_linkage"] != entry["source_linkage"] or \
                recorded["registry"] != "bridge/obligations.json" or \
                recorded["verification"] != "bridge/audit/results/verification.json" or \
                not entry["generated_files"] or not set(entry["generated_files"]) <= copies:
            raise RuntimeError("coverage claim lacks exact source/generated/challenge linkage: " + native_id)
        association = {"native_item_id": native_id,
                       "generated_declaration": entry["generated_declaration"],
                       "generated_file": entry["generated_file"]}
        declaration = entry["generated_declaration"].removeprefix("bulksketch.")
        if association not in linkage["source_definitions"] or \
                entry["generated_file"] not in entry["generated_files"] or \
                not re.search(r"^def\s+" + re.escape(declaration) + r"(?=\s|\(|\{)",
                              (ROOT / entry["generated_file"]).read_text(), re.MULTILINE):
            raise RuntimeError("generated declaration is not bound to the source-linked file: " + native_id)
    stateful_entries = registry.get("stateful_llbc_refinements", [])
    stateful_ids = {entry["native_item_id"] for entry in stateful_entries}
    stateful_evidence = {item["id"] for item in coverage["items"] if item.get("stateful_llbc_refinement_evidence")}
    if (len(stateful_ids) != len(stateful_entries) or stateful_ids != set(stateful_by_id) or
            stateful_evidence != stateful_ids or stateful_ids & set(refined) or
            coverage["proof_progress"].get("checked_stateful_llbc_refinements", 0) != len(stateful_entries)):
        raise RuntimeError("stateful LLBC evidence is missing, stale or double-counted")
    for entry in stateful_entries:
        native_id = entry["native_item_id"]
        stateful = stateful_by_id[native_id]
        recorded = items[native_id]["stateful_llbc_refinement_evidence"]
        match = next((event for event in events if event["kind"] == "challenge_match" and
                      event["challenge"] == entry["challenge"] and event["theorem"] == entry["theorem"]), None)
        program = entry["program"]
        name = program.rsplit(".", 1)[-1]
        if (source_items[native_id]["kind"] != "function" or
                entry["source_line_span_sha256"] != source_items[native_id]["source_line_span_sha256"] or
                items[native_id]["source_line_span_sha256"] != source_items[native_id]["source_line_span_sha256"] or
                entry["program_file"] != stateful["program_file"] or
                entry["llbc_sha256"] != stateful["llbc_sha256"] or
                program != stateful["programs"][native_id] or match is None or
                program not in match["referenced_constants"] or
                not re.search(r"^def\s+" + re.escape(name) + r"(?=\s|\()",
                              (ROOT / entry["program_file"]).read_text(), re.MULTILINE) or
                recorded != {key: entry[key] for key in ("theorem", "program", "scope")}):
            raise RuntimeError("stateful LLBC contract lacks exact source/program/challenge linkage: " + native_id)
    for event in roots:
        if set(event["axioms"]) - set(scope["permitted_axioms"]):
            raise RuntimeError("nonstandard bridge axiom")
    (RESULTS / "axioms.json").write_text(json.dumps(events, indent=2) + "\n")
    export = RESULTS / "bridge.export.ndjson"
    args = ["elan", "run", CHAIN, "lake", "env", "leanexport", "BulksketchBridge", "--"]
    args += sorted(names)
    start = time.monotonic()
    with export.open("w") as out, (RESULTS / "export.stderr.log").open("w") as err:
        result = subprocess.run(args, cwd=BRIDGE, env=ENV, stdin=subprocess.DEVNULL,
                                stdout=out, stderr=err, timeout=120)
    if result.returncode: raise RuntimeError("bridge export failed")
    records.append({"name": "export", "command": args, "exit_code": 0,
                    "sha256": sha(export), "bytes": export.stat().st_size,
                    "elapsed_seconds": time.monotonic() - start})
    prefix = Path(subprocess.check_output(["elan", "run", CHAIN, "lean", "--print-prefix"], text=True).strip())
    selector = RESULTS / "core-literal-selector.export.ndjson"
    selector_args = ["elan", "run", CHAIN, "lake", "env", "leanexport", "BulksketchBridge", "--",
                     "String.ofList", "Char.ofNat"]
    with selector.open("w") as out, (RESULTS / "literal-selector.stderr.log").open("w") as err:
        result = subprocess.run(selector_args, cwd=BRIDGE, env=ENV, stdin=subprocess.DEVNULL,
                                stdout=out, stderr=err, timeout=120)
    if result.returncode:
        raise RuntimeError("core literal selector export failed")
    prelude = RESULTS / "core-literal-prelude.export.ndjson"
    result, _ = run("project-core-literal-prelude", ["python3", str(ROOT / "scripts/project_core_prelude.py"),
        "--selector", str(selector), "--main", str(export), "--output", str(prelude)])
    result["selector_sha256"] = sha(selector)
    result["prelude_sha256"] = sha(prelude)
    records.append(result)
    result, _ = run("lean-core-prelude-replay", [str(prefix / "bin/leanchecker"),
                                               "--from-export", str(prelude)], timeout=120)
    records.append(result)
    result, _ = run("lean-kernel-replay", [str(ROOT / ".lake/build/bin/replay_export"),
                                          str(prelude), str(export)], timeout=120)
    records.append(result)
    config = {"use_stdin": False, "export_file_path": str(export),
              "permitted_axioms": scope["permitted_axioms"],
              "unpermitted_axiom_hard_error": True, "num_threads": 2,
              "nat_extension": True, "string_extension": True}
    (RESULTS / "nanoda.json").write_text(json.dumps(config, indent=2) + "\n")
    result, _ = run("independent-nanoda-replay", [str(prefix / "bin/nanoda_bin"),
                                                str(RESULTS / "nanoda.json")], timeout=120)
    records.append(result)
    summary = {"status": "passed", "source_commit": scope["source_commit"], "checkout_commit": head,
               "runtime_commit": runtime_head,
               "reviewed_translator_variants": [item["id"] for item in variants],
               "checked_generated_body_refinements": [entry["label"] for entry in registry["refinements"]],
               "checked_stateful_llbc_refinements": [entry["native_item_id"] for entry in stateful_entries],
               "frozen_challenges_matched": len(challenges),
               "axioms_used": sorted({axiom for event in roots for axiom in event["axioms"]}),
               "kernel_replay_loader": {"source": "tooling/ReplayExport.lean",
                   "source_sha256": sha(ROOT / "tooling/ReplayExport.lean"),
                   "executable_sha256": sha(ROOT / ".lake/build/bin/replay_export"),
                   "purpose": "schedule implicit core string-literal dependencies; unchanged parser/kernel/replay and original main export; every declaration checked or exact checked-prelude duplicate"},
               "checks": records, "whole_native_coverage_achieved": False,
               "trust_boundary": "pinned Charon/Aeneas translation, concrete Rust std Option/scalar models, source/extraction-compiler correspondence, Rust compiler and machine semantics; no application axioms"}
    (RESULTS / "verification.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({key: summary[key] for key in ["status", "checked_generated_body_refinements",
        "checked_stateful_llbc_refinements", "frozen_challenges_matched", "axioms_used", "whole_native_coverage_achieved"]}, indent=2))


if __name__ == "__main__":
    RESULTS.mkdir(parents=True, exist_ok=True)
    (RESULTS / "verification.json").write_text(json.dumps({"status": "running"}) + "\n")
    try:
        main()
    except Exception as error:
        (RESULTS / "verification.json").write_text(json.dumps({"status": "failed", "error": str(error)}, indent=2) + "\n")
        raise
