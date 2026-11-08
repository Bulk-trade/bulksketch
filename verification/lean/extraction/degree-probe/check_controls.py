#!/usr/bin/env python3
"""Reject changed DegreeProbe programs, scoped bindings, and source evidence."""
import json
from pathlib import Path
import shutil
import tempfile

from project import ACTIVE, DEPENDENCIES, DIRECTORY, GUARD, ROOT, RUNTIME, SOURCE, check


def reject(root, file, label, mutate, expected):
    path = root / file
    original = path.read_text()
    changed = mutate(original)
    if changed == original:
        raise RuntimeError(f"DegreeProbe control did not change the fixture: {label}")
    path.write_text(changed)
    try:
        check(root)
    except ValueError as error:
        if expected not in str(error):
            raise
        print(f"rejected {label}")
    else:
        raise RuntimeError(f"accepted altered DegreeProbe fixture: {label}")
    finally:
        path.write_text(original)


def edit_receipt(text, command, **fields):
    receipt = json.loads(text)
    next(item for item in receipt["checks"] if item["name"] == command).update(fields)
    return json.dumps(receipt)


def main():
    check()
    with tempfile.TemporaryDirectory(prefix="degree-probe-projection-") as path:
        repo = Path(path)
        root = repo / "verification/lean"
        shutil.copytree(ROOT / DIRECTORY, root / DIRECTORY)
        dependencies = [ACTIVE, RUNTIME, *(Path("bridge") / file for file in DEPENDENCIES),
            Path("bridge/Arithmetic/ReconstructionTypes.lean"), Path("bridge/Arithmetic/RebuiltLfsrGenerated.lean"),
            GUARD / "receipt.json", GUARD / "translator/checked-nested-slice-loan-retry.patch"]
        for file in dependencies:
            target = root / file
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / file, target)
        (repo / SOURCE).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(ROOT.parents[1] / SOURCE, repo / SOURCE)
        check(root)
        receipt = DIRECTORY / "receipt.json"
        reject(root, ACTIVE, "changed canonicalization dictionary",
            lambda text: text.replace("core.slice.Slice.sort_unstable core.cmp.OrdU64 s", "core.slice.Slice.sort_unstable core.cmp.OrdUsize s", 1),
            "compiled DegreeProbe projection differs")
        reject(root, ACTIVE, "changed constructor bound",
            lambda text: text.replace("capacity >= 3#usize", "capacity >= 4#usize", 1),
            "compiled DegreeProbe projection differs")
        reject(root, RUNTIME, "changed unsigned comparator",
            lambda text: text.replace("left.val ≤ right.val", "right.val ≤ left.val", 1),
            "DegreeProbe scoped runtime differs")
        reject(root, receipt, "wrong checked replay input",
            lambda text: edit_receipt(text, "replay", input_sha256="0" * 64), "DegreeProbe translator log, input, or flags differ")
        reject(root, receipt, "missing artifact manifest",
            lambda text: json.dumps(json.loads(text) | {"files_sha256": {}}), "incomplete DegreeProbe artifact set")
        reject(root, Path("bridge/Arithmetic/NewtonGuardGenerated.lean"), "changed shared guard declaration",
            lambda text: text.replace("guard_loop0.body", "guard_loop0.changed", 1), "shared DegreeProbe declarations differ")


if __name__ == "__main__":
    main()
