#!/usr/bin/env python3
"""Reject altered guard bodies, source evidence and translator controls."""
import json
from pathlib import Path
import shutil
import tempfile

from project import ACTIVE, DIRECTORY, GENERATED, ROOT, SHARED_TYPES, SOURCE, check


def reject(root, file, label, mutate, expected):
    path = root / file
    original = path.read_text()
    changed = mutate(original)
    if changed == original:
        raise RuntimeError(f"Newton guard control did not change the fixture: {label}")
    path.write_text(changed)
    try:
        check(root)
    except ValueError as error:
        if expected not in str(error):
            raise
        print(f"rejected {label}")
    else:
        raise RuntimeError(f"accepted altered Newton guard fixture: {label}")
    finally:
        path.write_text(original)


def edit_receipt(text, command, **fields):
    receipt = json.loads(text)
    entry = next(item for item in receipt["checks"] if item["name"] == command)
    entry.update(fields)
    return json.dumps(receipt)


def main():
    check()
    with tempfile.TemporaryDirectory(prefix="newton-guard-projection-") as path:
        repo = Path(path)
        root = repo / "verification/lean"
        shutil.copytree(ROOT / DIRECTORY, root / DIRECTORY)
        dependencies = [ACTIVE, *map(Path, SHARED_TYPES)]
        for module in ("quartic", "deg34-normalize"):
            folder = Path("extraction") / module
            dependencies.extend([folder / "arithmetic.llbc", *(folder / "Arithmetic" / file for file in GENERATED)])
        for file in dependencies:
            target = root / file
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / file, target)
        (repo / SOURCE).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(ROOT.parents[1] / SOURCE, repo / SOURCE)
        check(root)
        receipt = DIRECTORY / "receipt.json"
        reject(root, ACTIVE, "changed denominator write",
            lambda text: text.replace("Slice.update out1 5#usize a", "Slice.update out1 4#usize a", 1),
            "compiled Newton guard projection differs")
        reject(root, ACTIVE, "changed residual coefficient read",
            lambda text: text.replace("Slice.index_usize out i2", "Slice.index_usize odd i2", 1),
            "compiled Newton guard projection differs")
        reject(root, receipt, "wrong checked replay input",
            lambda text: edit_receipt(text, "replay", input_sha256="0" * 64), "Newton guard replay input differs")
        reject(root, receipt, "missing artifact manifest",
            lambda text: json.dumps(json.loads(text) | {"files_sha256": {}}), "incomplete Newton guard artifact set")
        reject(root, receipt, "changed unchecked outcome",
            lambda text: edit_receipt(text, "unchecked", exit_code=0), "Newton guard translator command matrix differs")
        reject(root, Path("extraction/quartic/Arithmetic/Types.lean"), "changed unrelated control output",
            lambda text: text + "\n", "Newton guard translator control outputs differ")


if __name__ == "__main__":
    main()
