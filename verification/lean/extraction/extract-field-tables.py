#!/usr/bin/env python3
"""Read only the reviewed fixed GF64 integer tables; emit literal proof data.

The transpose is untrusted generated certificate data and is separately checked
in Lean. This utility translates no application function or control flow.
"""
import ast
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
scope = json.loads((ROOT / "scope.json").read_text())
SOURCE = (ROOT / scope["source_repository"]).resolve()
inventory = json.loads((ROOT / "audit/source-inventory.json").read_text())
for item in inventory["files"]:
    if hashlib.sha256((SOURCE / item["path"]).read_bytes()).hexdigest() != item["sha256"]:
        raise SystemExit("native source drift: " + item["path"])
for path, expected in scope["source_build_inputs_sha256"].items():
    if hashlib.sha256((SOURCE / path).read_bytes()).hexdigest() != expected:
        raise SystemExit("native build input drift: " + path)


def read_literal(path, pattern):
    text = (SOURCE / path).read_text()
    matches = list(re.finditer(pattern, text, re.MULTILINE | re.DOTALL))
    if len(matches) != 1:
        raise ValueError("expected one exact fixed-table initializer: " + path)
    literal = matches[0]["literal"]
    if re.sub(r"0x[0-9a-fA-F_]+|[\s,\[\]]", "", literal):
        raise ValueError("unsupported token in fixed table")
    return ast.literal_eval(literal)


rows = read_literal("src/field/maps.rs",
    r"^const GF64_QUADRATIC:\s*\[u64;\s*64\]\s*=\s*(?P<literal>\[.*?^\]);")
chunks = read_literal("src/field/quadratic_chunks.rs",
    r"^pub\(super\) const GF64_QUADRATIC_CHUNKS:\s*\[\[u64;\s*16\];\s*16\]\s*=\s*(?P<literal>\[.*?^\]);")
if len(rows) != 64 or len(chunks) != 16 or any(len(row) != 16 for row in chunks):
    raise ValueError("wrong fixed-table dimensions")
if any(type(word) is not int or not 0 <= word < 2**64 for word in rows + sum(chunks, [])):
    raise ValueError("non-u64 table entry")
columns = [sum(((row >> index) & 1) << output for output, row in enumerate(rows))
           for index in range(64)]
lines = ["import Std", "", "-- GENERATED literal data from the reviewed native tables.",
         "-- Column transposition and all map identities are separately proved in Lean.",
         "namespace BulksketchProofs.Generated.FieldTables", "",
         "def quadraticRows : List (BitVec 64) := ["]
lines += ["  " + ", ".join(f"0x{value:016x}" for value in rows[i:i+4]) + ("," if i < 60 else "")
          for i in range(0, 64, 4)]
lines += ["]", "", "def quadraticChunks : List (List (BitVec 64)) := ["]
for index, row in enumerate(chunks):
    lines += ["  [" + ", ".join(f"0x{value:016x}" for value in row) + "]" + ("," if index < 15 else "")]
lines += ["]", "", "def quadraticColumns : List (BitVec 64) := ["]
lines += ["  " + ", ".join(f"0x{value:016x}" for value in columns[i:i+4]) + ("," if i < 60 else "")
          for i in range(0, 64, 4)]
lines += ["]", "", "end BulksketchProofs.Generated.FieldTables", ""]
output = ROOT / "BulksketchProofs/Generated/FieldTables.lean"
output.write_text("\n".join(lines))
receipt = {"source_commit": scope["source_commit"],
           "source_files": {path: hashlib.sha256((SOURCE / path).read_bytes()).hexdigest()
                            for path in ["src/field/maps.rs", "src/field/quadratic_chunks.rs"]},
           "row_entries": 64, "chunk_entries": 256, "derived_transpose_entries": 64,
           "output": str(output.relative_to(ROOT)),
           "output_sha256": hashlib.sha256(output.read_bytes()).hexdigest(),
           "trust": "strict integer-literal extraction only; transpose and mathematical claims require Lean proofs"}
(ROOT / "extraction/field-tables-linkage.json").write_text(json.dumps(receipt, indent=2) + "\n")
print(json.dumps(receipt, indent=2))
