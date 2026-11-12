#!/usr/bin/env python3
"""Exercise the stock and scoped checked replay gates in an isolated shadow."""
import json
from pathlib import Path
from tempfile import TemporaryDirectory

import project


def run():
    root = project.ROOT
    project.check(root)
    destination = project.DIRECTORY / "receipt.json"
    with TemporaryDirectory() as location:
        repo = Path(location)
        shadow = repo / "verification/lean"
        required = [(root, shadow, project.DIRECTORY / path) for path in project.ARTIFACTS]
        required += [(root, shadow, Path(path)) for path in (
            *project.SHARED, project.TINY, project.COMPLETED,
            *(project.COMPATIBILITY / name for name in project.OUTPUTS))]
        required += [(root.parents[1], repo, Path(path)) for path in project.SOURCE]
        for original, destination_root, path in required:
            target = destination_root / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.symlink_to(original / path)
        for label in ("checked", "wrong-assert"):
            receipt = json.loads((root / destination).read_text())
            if label == "checked":
                receipt["completed"]["controls"][label]["command"].remove("-checks")
            else:
                receipt["completed"]["controls"][label]["status"] = 0
            (shadow / destination).write_text(json.dumps(receipt))
            try:
                project.check(shadow)
            except ValueError as error:
                if str(error) != "public lifecycle completed-result guard matrix differs: " + label:
                    raise
                print("rejected", label)
            else:
                raise ValueError("invalid control accepted: " + label)


if __name__ == "__main__":
    run()
