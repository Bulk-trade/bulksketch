#!/usr/bin/env python3
"""Select original portable arithmetic and real Gf64 constants; preserve tool results.

Native source is read only. Generated files and failures remain in this directory;
this script does not copy or edit any bridge/application Lean body.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

PROOF = Path(__file__).resolve().parents[2]
OUT = Path(__file__).resolve().parent
PINS = {
    "charon": "7b462d9159db2ed3015162352183906a30bfafc6",
    "aeneas": "ab34bd28458a08c150b7cbf1873e59af74588138",
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def logged(directory, label, command, environment, source):
    start = time.monotonic()
    log = directory / (label + ".log")
    with log.open("w") as stream:
        result = subprocess.run(command, cwd=source, env=environment,
                                stdin=subprocess.DEVNULL, stdout=stream,
                                stderr=subprocess.STDOUT, timeout=300)
    receipt = {"command": command, "exit_code": result.returncode,
               "elapsed_seconds": time.monotonic() - start,
               "log": str(log.relative_to(PROOF)), "log_sha256": sha(log)}
    (directory / (label + ".status.json")).write_text(json.dumps(receipt, indent=2) + "\n")
    print(label, "exit", result.returncode, flush=True)
    return receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--charon", type=Path, required=True)
    parser.add_argument("--aeneas", type=Path, required=True)
    parser.add_argument("--label", required=True)
    parser.add_argument("--start-from", action="append", default=[],
                        help="additional source root; repeat without changing the baseline roots")
    parser.add_argument("--impl-selector", default="{impl bulksketch::field::BinaryField for bulksketch::field::Gf64}")
    arguments = parser.parse_args()
    scope = json.loads((PROOF / "scope.json").read_text())
    source = (PROOF / scope["source_repository"]).resolve()
    inventory = json.loads((PROOF / "audit/source-inventory.json").read_text())
    for item in inventory["files"]:
        if sha(source / item["path"]) != item["sha256"]:
            raise SystemExit("native source drift: " + item["path"])
    for path, expected in scope["source_build_inputs_sha256"].items():
        if sha(source / path) != expected:
            raise SystemExit("native build-input drift: " + path)
    tools = {"charon": arguments.charon.resolve(strict=True),
             "aeneas": arguments.aeneas.resolve(strict=True)}
    for label, binary in tools.items():
        head = subprocess.check_output(["git", "-C", str(binary.parent), "rev-parse", "HEAD"], text=True).strip()
        if head != PINS[label]:
            raise SystemExit(label + " source pin mismatch")
        if subprocess.run(["git", "-C", str(binary.parent), "diff", "--quiet"]).returncode:
            raise SystemExit(label + " source checkout is dirty")
    directory = OUT / arguments.label
    directory.mkdir(parents=True, exist_ok=True)
    llbc = directory / "arithmetic.llbc"
    generated = directory / "Arithmetic"
    generated.mkdir(exist_ok=True)
    environment = dict(os.environ, RUSTUP_TOOLCHAIN="nightly-2026-09-17",
                       CARGO_TARGET_DIR=str(PROOF / "tooling/canonical-arithmetic-charon-target"),
                       CARGO_BUILD_JOBS="1")
    roots = ["bulksketch::field::gf64::square", "bulksketch::field::gf64::raw_mul",
             "bulksketch::field::gf64::mul", arguments.impl_selector]
    roots += arguments.start_from
    command = [str(tools["charon"]), "cargo", "--preset=aeneas", "--sysroot=default",
               "--dest-file=" + str(llbc)]
    command += ["--start-from=" + root for root in roots]
    command += ["--", "--manifest-path", str(source / "Cargo.toml"),
                "-p", "bulksketch", "--lib", "--locked"]
    charon = logged(directory, "charon", command, environment, source)
    receipt = {"source_commit": scope["source_commit"],
               "checkout_commit": subprocess.check_output(["git", "-C", str(source), "rev-parse", "HEAD"], text=True).strip(),
               "native_files_checked": len(inventory["files"]), "build_inputs_checked": len(scope["source_build_inputs_sha256"]),
               "tool_commits": PINS, "tool_binary_sha256": {label: sha(binary) for label, binary in tools.items()},
               "rust_toolchain": "nightly-2026-09-17", "selected_roots": roots,
               "charon": charon, "application_source_edited": False,
               "bridge_files_edited": False, "implementation_proof_credit": 0}
    if charon["exit_code"] or not llbc.exists():
        receipt["status"] = "charon_failed"
    else:
        payload = json.loads(llbc.read_text())
        receipt["llbc_has_errors"] = payload.get("has_errors")
        receipt["llbc_sha256"] = sha(llbc)
        receipt["declaration_counts"] = {name: len(payload["translated"][name]) for name in
                                          ["fun_decls", "type_decls", "global_decls", "trait_impls"]}
        if payload.get("has_errors") is not False:
            receipt["status"] = "incomplete_llbc"
        else:
            aeneas = logged(directory, "aeneas", [str(tools["aeneas"]), "-backend", "lean",
                "-split-files", "-dest", str(generated), str(llbc)], environment, source)
            receipt["aeneas"] = aeneas
            receipt["status"] = "generated" if aeneas["exit_code"] == 0 else "aeneas_failed"
            receipt["generated"] = [{"path": str(p.relative_to(PROOF)), "sha256": sha(p)}
                                    for p in sorted(generated.glob("*.lean"))]
    (directory / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({key: receipt[key] for key in ["status", "selected_roots"]}, indent=2))
    if receipt["status"] != "generated":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
