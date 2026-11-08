#!/usr/bin/env python3
"""Mutate independent fixture copies of the native normalization projection."""
import json
from pathlib import Path
import shutil
import tempfile

from project import ACTIVE, DIRECTORY, ROOT, SHARED, check


def verify_rejection(root, path, name, change, reason):
    path = root / path
    original = path.read_text()
    path.write_text(change(original))
    try:
        check(root)
    except ValueError as error:
        if reason not in str(error):
            raise
        print(f"rejected {name}")
    else:
        raise RuntimeError(f"modified normalization fixture accepted: {name}")
    finally:
        path.write_text(original)


def main():
    check()
    with tempfile.TemporaryDirectory(prefix="normalize-projection-") as path:
        repo = Path(path)
        root = repo / "verification/lean"
        for file in (DIRECTORY, ACTIVE, *(Path(file) for file in SHARED)):
            target = root / file
            target.parent.mkdir(parents=True, exist_ok=True)
            if (ROOT / file).is_dir():
                shutil.copytree(ROOT / file, target)
            else:
                shutil.copy2(ROOT / file, target)
        source = Path("src/decode/deg34.rs")
        (repo / source).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(ROOT.parents[1] / source, repo / source)
        check(root)
        verify_rejection(root, DIRECTORY / "receipt.json", "missing raw artifacts",
            lambda text: json.dumps(json.loads(text) | {"artifacts": []}), "incomplete normalization extraction receipt")
        verify_rejection(root, ACTIVE, "wrong final coefficient slot",
            lambda text: text.replace("Slice.update factor2 degree 1#u64", "Slice.update factor2 i2 1#u64"),
            "compiled normalization projection differs")
        verify_rejection(root, ACTIVE, "wrong denominator slot",
            lambda text: text.replace("Slice.index_usize cleared 5#usize", "Slice.index_usize cleared 4#usize"),
            "compiled normalization projection differs")
        verify_rejection(root, repo / source, "changed Rust input",
            lambda text: text + "\n", "frozen normalization source differs")


if __name__ == "__main__":
    main()
