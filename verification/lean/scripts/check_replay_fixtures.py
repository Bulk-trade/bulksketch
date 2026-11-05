#!/usr/bin/env python3
"""Exercise the kernel replay loader with actual corrupted exported declarations.

Original proof exports, Lean sources, and frozen specifications are never edited.
"""
from pathlib import Path
import hashlib
import json
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
RESULTS = ROOT / "bridge/audit/results"
OUTPUT = RESULTS / "replay-negative"
MAIN = RESULTS / "bridge.export.ndjson"
PRELUDE = RESULTS / "core-literal-prelude.export.ndjson"
DRIVER = ROOT / ".lake/build/bin/replay_export"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def corrupt_exports():
    mutations = {
        "bad-proof": ("thm", "BulksketchBridge.RawMul.raw_mul_refines", "value"),
        "conflicting-preload": ("def", "String.ofList", "value"),
        "unsafe-declaration": ("def", "bulksketch.field.gf64.raw_mul", "unsafe"),
        "partial-declaration": ("def", "bulksketch.field.gf64.raw_mul", "partial"),
    }
    names = {0: ""}
    declared_names = set()
    unused_candidates = []
    string_definition = None
    changed = {case: 0 for case in mutations}
    handles = {case: (OUTPUT / (case + ".ndjson")).open("w") for case in mutations}
    try:
        for line in MAIN.open():
            record = json.loads(line)
            if "in" in record:
                component = record.get("str", record.get("num"))
                suffix = str(component.get("str", component.get("i")))
                parent = names[component["pre"]]
                names[record["in"]] = parent + ("." if parent else "") + suffix
                if component["pre"] == 0 and suffix == "u":
                    unused_candidates.append(record["in"])
            if "inductive" in record:
                for group in ("types", "ctors", "recs"):
                    declared_names.update(item["name"] for item in record["inductive"][group])
            for kind in ("def", "thm", "axiom", "opaque", "quot"):
                if kind in record:
                    declared_names.add(record[kind]["name"])
            if "def" in record and names[record["def"]["name"]] == "String.ofList":
                string_definition = dict(record["def"])
            for case, (kind, target, change) in mutations.items():
                declaration = record.get(kind)
                if declaration and names[declaration["name"]] == target:
                    altered = dict(declaration)
                    if change == "value":
                        # The proposition/type itself is not a proof/value of that type.
                        altered["value"] = declaration["type"]
                    else:
                        altered["safety"] = change
                    handles[case].write(json.dumps({kind: altered}, separators=(",", ":")) + "\n")
                    changed[case] += 1
                else:
                    handles[case].write(line)
    finally:
        for handle in handles.values():
            handle.close()
    if set(changed.values()) != {1}:
        raise RuntimeError("each negative export must alter exactly one real declaration: " + str(changed))
    unused = next((name for name in unused_candidates if name not in declared_names), None)
    if unused is None or string_definition is None:
        raise RuntimeError("could not construct a valid extra-prelude definition")
    string_definition.update({"name": unused, "all": [unused]})
    # This is a valid, closed additional definition; it must be rejected because
    # the prelude may reorder declarations, but may not extend the environment.
    with (OUTPUT / "extra-prelude.ndjson").open("wb") as output:
        output.write(PRELUDE.read_bytes())
        output.write((json.dumps({"def": string_definition}, separators=(",", ":")) + "\n").encode())


def main():
    OUTPUT.mkdir(parents=True, exist_ok=True)
    before = {str(path): digest(path) for path in [MAIN, PRELUDE]}
    corrupt_exports()
    forbidden = ROOT / "audit/results/negative/forbidden.export.ndjson"
    cases = [
        ("bad-proof", PRELUDE, OUTPUT / "bad-proof.ndjson", "type mismatch"),
        ("conflicting-preload", PRELUDE, OUTPUT / "conflicting-preload.ndjson", "conflicting preloaded declaration"),
        ("unsafe-declaration", PRELUDE, OUTPUT / "unsafe-declaration.ndjson", "unsafe or partial declaration"),
        ("partial-declaration", PRELUDE, OUTPUT / "partial-declaration.ndjson", "unsafe or partial declaration"),
        ("extra-prelude", OUTPUT / "extra-prelude.ndjson", MAIN, "prelude: declaration absent from main export"),
        ("forbidden-main-axiom", PRELUDE, forbidden, "main: unpermitted axiom"),
        ("forbidden-prelude-axiom", forbidden, MAIN, "prelude: unpermitted axiom"),
    ]
    results = []
    for case, prelude, proof, expected in cases:
        start = time.monotonic()
        result = subprocess.run([str(DRIVER), str(prelude), str(proof)], stdin=subprocess.DEVNULL,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=120)
        (OUTPUT / (case + ".log")).write_text(result.stdout)
        if result.returncode == 0 or expected not in result.stdout:
            raise RuntimeError("negative replay did not reject for the expected reason: " + case + "\n" + result.stdout[-3000:])
        results.append({"case": case, "status": "expected_rejection_confirmed",
                        "exit_code": result.returncode, "elapsed_seconds": time.monotonic() - start,
                        "expected_diagnostic": expected})
    if any(digest(Path(path)) != expected for path, expected in before.items()):
        raise RuntimeError("a production proof export changed during negative checking")
    summary = {"status": "passed", "original_exports_unchanged": True, "cases": results}
    (RESULTS / "replay-negative-fixtures.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
