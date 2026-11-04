#!/usr/bin/env python3
"""Compare exact original generated declarations, never a prefix match."""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
OUT = Path(__file__).resolve().parent


def definition(path, declaration):
    source = path.read_text()
    pattern = re.compile(r"^def\s+" + re.escape(declaration) + r"(?=\s|\(|\{)", re.MULTILINE)
    matches = list(pattern.finditer(source))
    if len(matches) != 1:
        raise RuntimeError(f"expected exactly one exact declaration {declaration} in {path}")
    start = matches[0].start()
    stop = re.search(r"\n(?=/--|end bulksketch\b)", source[start:])
    if stop is None:
        raise RuntimeError("could not find declaration boundary for " + declaration)
    return source[start:start + stop.start()].rstrip() + "\n", source[:start].count("\n") + 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--previous-square", type=Path)
    arguments = parser.parse_args()
    canonical = ROOT / "bridge/Arithmetic/Funs.lean"
    pairs = [(name, ROOT / "extraction/reduce/Reduce/Funs.lean") for name in [
        "field.gf64.reduce_loop0_loop0.body", "field.gf64.reduce_loop0_loop0",
        "field.gf64.reduce_loop0.body", "field.gf64.reduce_loop0", "field.gf64.reduce"]]
    pairs.append(("field.gf64.spread", ROOT / "extraction/spread/generated/Funs.lean"))
    if arguments.previous_square:
        pairs.append(("field.gf64.square", arguments.previous_square.resolve(strict=True)))
    receipt = OUT / "migration-receipt.json"
    previous = receipt.read_bytes()
    record = json.loads(previous)
    checks = {}
    for name, original in pairs:
        before, before_line = definition(original, name)
        after, after_line = definition(canonical, name)
        if before != after:
            raise RuntimeError("original definition text changed: " + name)
        checks[name] = {"exact_definition_text_equal": True,
                       "definition_sha256": hashlib.sha256(before.encode()).hexdigest(),
                       "reference": str(original), "reference_definition_line": before_line,
                       "canonical_definition_line": after_line}
        print(name, before_line, after_line, checks[name]["definition_sha256"])
    # The leading declaration name is part of each compared text/hash.
    if len({check["definition_sha256"] for check in checks.values()}) != len(checks):
        raise RuntimeError("distinct named declarations unexpectedly share an exact-text hash")
    checks["shared_type_declarations"] = record["original_definition_checks"]["shared_type_declarations"]
    record["original_definition_checks"] = checks
    record["definition_selector"] = "unique multiline ^def FULLNAME followed by whitespace, ( or {"
    record["comparison_correction"] = {
        "reason": "Previous str.index prefix lookup could select an earlier reduce helper; exact-name selection now independently rerun.",
        "superseded_receipt_sha256": hashlib.sha256(previous).hexdigest(),
        "generated_files_modified": False,
        "trailing_whitespace_at_definition_end_only_normalized": True}
    receipt.write_text(json.dumps(record, indent=2) + "\n")


if __name__ == "__main__":
    main()
