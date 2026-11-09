#!/usr/bin/env python3
"""Check that the encoder projection rejects incomplete checked replay."""
import json
from pathlib import Path
from tempfile import TemporaryDirectory

import project


def run():
    root = project.ROOT
    project.check(root)
    receipt_path = project.DIRECTORY / "receipt.json"
    required = [project.DIRECTORY / item for item in project.ARTIFACTS]
    required += [project.ACTIVE, project.SINGLE, *map(Path, project.SHARED),
                 Path("extraction/avx-linear-entry/receipt.json")]
    with TemporaryDirectory() as location:
        repo = Path(location)
        shadow = repo / "verification/lean"
        for source_root, target_root, item in (
            *((root, shadow, path) for path in required),
            (root.parents[1], repo, Path(project.SOURCE)),
        ):
            target = target_root / item
            target.parent.mkdir(parents=True, exist_ok=True)
            target.symlink_to(source_root / item)
        for lane in project.TARGETS:
            receipt = json.loads((root / receipt_path).read_text())
            receipt["captures"][lane]["commands"]["replay"]["command"].remove("-checks")
            (shadow / receipt_path).write_text(json.dumps(receipt))
            try:
                project.check(shadow)
            except ValueError as error:
                if str(error) != "AVX encode checked replay differs: " + lane:
                    raise
                print("rejected", lane)
            else:
                raise ValueError("unchecked replay accepted: " + lane)


if __name__ == "__main__":
    run()
