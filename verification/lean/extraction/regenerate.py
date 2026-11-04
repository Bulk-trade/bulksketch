#!/usr/bin/env python3
"""Reproduce a narrow unverified AST-derived model; never claim a Rust proof."""
import hashlib
import json
import os
from pathlib import Path
import subprocess

PROOF = Path(__file__).resolve().parents[1]
SCOPE = json.loads((PROOF / 'scope.json').read_text())
SOURCE = (PROOF / SCOPE['source_repository']).resolve()
PIN = '0a5bda53f6b07fcae8acd870e2d0c4a246d207e6'
PATHS = ['src/field/gf64.rs', 'src/field/mod.rs', 'src/types.rs']

def sha(data):
    return hashlib.sha256(data).hexdigest()

def run(args, **kwargs):
    return subprocess.run(args, check=True, text=True, **kwargs)

head = run(['git', '-C', str(SOURCE), 'rev-parse', 'HEAD'], capture_output=True).stdout.strip()
inventory = json.loads((PROOF / 'audit/source-inventory.json').read_text())
if inventory['source_commit'] != PIN:
    raise SystemExit('source inventory does not match the reviewed commit')
expected_hashes = {item['path']: item['sha256'] for item in inventory['files']}
source_records = []
for path in PATHS:
    actual = (SOURCE / path).read_bytes()
    if sha(actual) != expected_hashes[path]:
        raise SystemExit(f'refusing modified native source: {path}')
    snapshot = PROOF / 'extraction/native-source' / path
    snapshot.parent.mkdir(parents=True, exist_ok=True)
    snapshot.write_bytes(actual)
    source_records.append({'path': path, 'sha256': sha(actual)})

manifest = PROOF / 'tooling/ast-extractor/Cargo.toml'
env = dict(os.environ)
env['CARGO_TARGET_DIR'] = str(PROOF / 'tooling/ast-extractor-target')
run(['cargo', '+1.96.1', 'build', '--release', '--locked',
     '--manifest-path', str(manifest), '-j', '2'], env=env)
output = PROOF / 'extraction/generated'
run([str(PROOF / 'tooling/ast-extractor-target/release/bulksketch-narrow-extractor'),
     str(SOURCE), str(output)])
body_hash = sha((output / 'reduce-rust-body.tokens').read_bytes())
header = ('-- Native source pin: ' + PIN + '\n'
          '-- Full reduce body normalized-token SHA256: ' + body_hash + '\n'
          '-- Source gf64.rs SHA256: ' + source_records[0]['sha256'] + '\n')
generated = header + (output / 'Reduce.lean').read_text()
destination = PROOF / 'BulksketchProofs/Generated/Reduce.lean'
destination.parent.mkdir(parents=True, exist_ok=True)
if not destination.exists() or destination.read_text() != generated:
    destination.write_text(generated)
record = {
    'schema': 'bulksketch-narrow-source-extraction-v1',
    'source_commit': PIN,
    'source_files': source_records,
    'source_item': 'bulksketch::field::gf64::reduce::<Gf64>',
    'normalised_full_body_sha256': body_hash,
    'selected_branch': 'F::BITS == 64',
    'selected_specialization_guard': 'Gf64::BITS = 64; checked from parsed native impl',
    'raw_product_fields': {'lo': 'u64', 'hi': 'u64'},
    'supported_branch_syntax': ['immutable let', 'RawProduct lo/hi fields',
        'bound identifier', 'u64 bitwise XOR', 'literal u64 left/right shift below64', 'parentheses'],
    'unsupported_ast_policy': 'reject; never emit opaque or assumed definitions',
    'excluded_branch': 'generic non-GF64 else; not claimed by this model',
    'generated_declaration': 'BulksketchProofs.Generated.reduceGf64',
    'generated_module': str(destination.relative_to(PROOF)),
    'generated_module_sha256': sha(destination.read_bytes()),
    'ast_sexpr_sha256': sha((output / 'reduce-gf64.ast.sexp').read_bytes()),
    'generator_source_sha256': sha((PROOF / 'tooling/ast-extractor/src/main.rs').read_bytes()),
    'generator_cargo_lock_sha256': sha((PROOF / 'tooling/ast-extractor/Cargo.lock').read_bytes()),
    'is_aeneas_generated': False,
    'translator_verified': False,
    'rust_semantic_refinement_proved': False,
    'implementation_proof_credit': 0,
}
(PROOF / 'extraction/reduce-gf64-linkage.json').write_text(json.dumps(record, indent=2) + '\n')
print('Generated exact-source-derived Lean expression; translator/Rust semantic bridge UNPROVED.')
