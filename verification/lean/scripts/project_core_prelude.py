#!/usr/bin/env python3
"""Select core declarations from a main export without rewriting any records."""
import argparse
import hashlib
import json
from pathlib import Path
import sys


def records(path):
    # Preserve Name identity: a string component containing a dot is not a
    # sequence of components, and numeric components differ from string ones.
    names = {0: ()}
    with path.open("rb") as source:
        for number, raw in enumerate(source, 1):
            item = json.loads(raw)
            if "in" in item:
                tag = "str" if "str" in item else "num"
                node = item[tag]
                component = node["str"] if tag == "str" else node["i"]
                names[item["in"]] = names[node["pre"]] + ((tag, component),)
            declared = []
            if "inductive" in item:
                for group in ("types", "ctors", "recs"):
                    declared.extend(names[node["name"]]
                                    for node in item["inductive"][group])
            else:
                for kind in ("def", "thm", "axiom", "opaque", "quot"):
                    if kind in item:
                        if declared:
                            raise ValueError(f"{path}:{number}: multiple declarations in one record")
                        declared = [names[item[kind]["name"]]]
            yield raw, declared


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--selector", required=True, type=Path)
    parser.add_argument("--main", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    if args.output.resolve() in (args.selector.resolve(), args.main.resolve()):
        raise ValueError("output must differ from both input paths")
    selected = {name for _, declared in records(args.selector) for name in declared}
    if not selected:
        raise ValueError("selector contains no declarations")
    seen = set()
    kept = 0
    omitted = 0
    with args.output.open("wb") as output:
        for raw, declared in records(args.main):
            if declared:
                included = selected.intersection(declared)
                if not included:
                    omitted += len(declared)
                    continue
                if not set(declared) <= selected:
                    raise ValueError("selector chooses only part of an inductive package")
                seen.update(declared)
                kept += len(declared)
            output.write(raw)
    if seen != selected:
        raise ValueError(f"main export is missing {len(selected - seen)} selected declarations")
    print(json.dumps({
        "selector_path": str(args.selector),
        "selector_sha256": sha(args.selector),
        "main_path": str(args.main),
        "main_sha256": sha(args.main),
        "output_path": str(args.output),
        "output_sha256": sha(args.output),
        "output_bytes": args.output.stat().st_size,
        "selected_declarations": kept,
        "omitted_declarations": omitted,
        "all_non_declaration_records_unchanged": True,
        "all_selected_declaration_records_unchanged": True,
    }, indent=2))


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"Core prelude projection rejected: {error}", file=sys.stderr)
        sys.exit(1)
