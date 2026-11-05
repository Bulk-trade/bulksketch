#!/usr/bin/env python3
"""Extract unchanged native spread only; preserve source/tool/output evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT.parents[1]
OUT = ROOT / 'extraction/spread'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run_logged(name, command, environment):
    log = OUT / (name + '.log')
    start = time.monotonic()
    with log.open('w') as stream:
        result = subprocess.run(command, cwd=SOURCE, env=environment,
                                stdin=subprocess.DEVNULL, stdout=stream,
                                stderr=subprocess.STDOUT, timeout=90)
    record = {'command': command, 'exit_code': result.returncode,
              'elapsed_seconds': time.monotonic() - start,
              'log': str(log.relative_to(ROOT)), 'log_sha256': digest(log)}
    (OUT / (name + '.status.json')).write_text(json.dumps(record, indent=2) + '\n')
    if result.returncode:
        raise RuntimeError(name + ' failed; inspect ' + str(log))
    return record


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--charon', type=Path, required=True)
    parser.add_argument('--aeneas', type=Path, required=True)
    options = parser.parse_args()
    charon = options.charon.resolve(strict=True)
    aeneas = options.aeneas.resolve(strict=True)
    scope = json.loads((ROOT / 'scope.json').read_text())
    inventory = json.loads((ROOT / 'audit/source-inventory.json').read_text())
    if inventory['source_commit'] != scope['source_commit']:
        raise RuntimeError('source inventory and reviewed source revision disagree')
    source_hashes = {}
    for item in inventory['files']:
        path = SOURCE / item['path']
        if digest(path) != item['sha256']:
            raise RuntimeError('reviewed native source changed: ' + item['path'])
        source_hashes[item['path']] = item['sha256']
    for name, expected in scope['source_build_inputs_sha256'].items():
        if digest(SOURCE / name) != expected:
            raise RuntimeError('reviewed native build input changed: ' + name)
    environment = dict(os.environ, RUSTUP_TOOLCHAIN='nightly-2026-09-17',
                       CARGO_TARGET_DIR=str(ROOT / 'tooling/spread-charon-target'),
                       CARGO_BUILD_JOBS='1')
    llbc = OUT / 'spread.llbc'
    destination = OUT / 'generated'
    destination.mkdir(exist_ok=True)
    print('Extracting original native spread body with pinned Charon', flush=True)
    charon_result = run_logged('charon', [str(charon), 'cargo', '--preset=aeneas',
        '--sysroot=default', '--dest-file=' + str(llbc),
        '--start-from=bulksketch::field::gf64::spread', '--', '--manifest-path',
        str(SOURCE / 'Cargo.toml'), '-p', 'bulksketch', '--lib', '--locked'], environment)
    payload = json.loads(llbc.read_text())
    if payload.get('has_errors') is not False:
        raise RuntimeError('LLBC is incomplete or lacks an explicit has_errors=false')
    print('Generating Lean from complete spread LLBC', flush=True)
    aeneas_result = run_logged('aeneas', [str(aeneas), '-backend', 'lean', '-split-files',
        '-dest', str(destination), str(llbc)], environment)
    copies = ROOT / 'bridge/Spread'
    copies.mkdir(exist_ok=True)
    generated = []
    for name in ['Types.lean', 'Funs.lean']:
        origin = destination / name
        target = copies / name
        shutil.copyfile(origin, target)
        generated.append({'source': str(origin.relative_to(ROOT)),
                          'copy': str(target.relative_to(ROOT)),
                          'sha256': digest(origin)})
        if origin.read_bytes() != target.read_bytes():
            raise RuntimeError('generated copy is not byte-identical')
    templates = [{'path': str(p.relative_to(ROOT)), 'sha256': digest(p)}
                 for p in sorted(destination.glob('*External*'))]
    record = {'schema': 'bulksketch-spread-actual-extraction-v1',
              'reviewed_native_revision': scope['source_commit'],
              'checkout_head': subprocess.check_output(
                  ['git', '-C', str(SOURCE), 'rev-parse', 'HEAD'], text=True).strip(),
              'selected_native_item': 'bulksketch::field::gf64::spread',
              'source_files_sha256': source_hashes,
              'build_inputs_sha256': scope['source_build_inputs_sha256'],
              'rust_toolchain': 'nightly-2026-09-17',
              'charon_commit': '7b462d9159db2ed3015162352183906a30bfafc6',
              'aeneas_commit': 'ab34bd28458a08c150b7cbf1873e59af74588138',
              'charon_executable_sha256': digest(charon),
              'aeneas_executable_sha256': digest(aeneas),
              'charon': charon_result, 'aeneas': aeneas_result,
              'llbc': str(llbc.relative_to(ROOT)), 'llbc_has_errors': False,
              'llbc_sha256': digest(llbc), 'generated_copies': generated,
              'external_templates': templates,
              'generated_body_modified': False,
              'source_body_refinement': 'not_yet_proved',
              'full_native_coverage_achieved': False}
    (OUT / 'source-linkage.json').write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps({'llbc_has_errors': False, 'generated_copies': generated,
                      'external_templates': templates}, indent=2), flush=True)


if __name__ == '__main__':
    main()
