#!/usr/bin/env python3
"""Fetch the pinned Lean runtime needed to check committed generated-body proofs.

This does not build Charon/OCaml or regenerate Rust extraction. Those tools are
needed only when intentionally regenerating the application bodies.
"""
import argparse
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
DESTINATION = ROOT / "tooling/aeneas"
COMMIT = "ab34bd28458a08c150b7cbf1873e59af74588138"
URL = "https://github.com/AeneasVerif/aeneas.git"
ENV = dict(os.environ, CI="1", MATHLIB_NO_CACHE_ON_UPDATE="1", LEAN_NUM_THREADS="2")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reuse", type=Path, help="reuse an existing clean checkout of the exact runtime pin")
    parser.add_argument("--skip-cache", action="store_true", help="build without downloading optional Mathlib artifacts")
    arguments = parser.parse_args()
    (ROOT / "tooling/logs").mkdir(parents=True, exist_ok=True)
    if arguments.reuse and not DESTINATION.exists():
        checkout = arguments.reuse.resolve()
        actual = subprocess.check_output(["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True).strip()
        if actual != COMMIT:
            raise SystemExit("reuse checkout does not match the pinned Aeneas revision")
        DESTINATION.symlink_to(checkout, target_is_directory=True)
    if not DESTINATION.exists():
        DESTINATION.mkdir(parents=True)
        subprocess.run(["git", "init", "--quiet", str(DESTINATION)], check=True)
        subprocess.run(["git", "-C", str(DESTINATION), "remote", "add", "origin", URL], check=True)
        subprocess.run(["git", "-C", str(DESTINATION), "fetch", "--depth", "1", "origin", COMMIT], check=True)
        subprocess.run(["git", "-C", str(DESTINATION), "checkout", "--detach", COMMIT], check=True)
    actual = subprocess.check_output(["git", "-C", str(DESTINATION), "rev-parse", "HEAD"], text=True).strip()
    if actual != COMMIT:
        raise SystemExit("runtime checkout differs from the reviewed pin")
    if subprocess.check_output(["git", "-C", str(DESTINATION), "status", "--porcelain"], text=True).strip():
        raise SystemExit("runtime checkout has unreviewed tracked or untracked changes")
    subprocess.run(["python3", str(ROOT / "tooling/bootstrap-lean-runtime.py")], env=ENV, check=True)
    if not arguments.skip_cache:
        subprocess.run(["python3", str(ROOT / "tooling/fetch-lean-runtime-cache.py")], env=ENV, check=True)
    # Cache and build in the consuming workspace. Building only the runtime's
    # own workspace leaves the bridge with a second uncached dependency tree.
    subprocess.run(["elan", "run", "leanprover/lean4:v4.35.0", "lake", "build", "Workmeter.Funs"],
                   cwd=ROOT / "bridge", env=ENV, check=True)


if __name__ == "__main__":
    main()
