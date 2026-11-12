#!/usr/bin/env python3
"""Regenerate actual WorkMeter methods from pinned native source content."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

PROOF = Path(__file__).resolve().parents[2]
SCOPE = json.loads((PROOF/'scope.json').read_text())
SOURCE = (PROOF/SCOPE['source_repository']).resolve()
PINS = {'charon':'7b462d9159db2ed3015162352183906a30bfafc6',
        'aeneas':'ab34bd28458a08c150b7cbf1873e59af74588138'}
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--charon',type=Path,default=PROOF/'tooling/charon/bin/charon')
parser.add_argument('--aeneas',type=Path,default=PROOF/'tooling/aeneas/src/_build/default/main.exe')
parser.add_argument('--output',type=Path,default=PROOF/'extraction/aeneas-pilot/workmeter-used-staging')
args=parser.parse_args()
args.charon=args.charon.resolve()
args.aeneas=args.aeneas.resolve()
args.output=args.output.resolve()
args.output.mkdir(parents=True,exist_ok=True)

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()

def logged(name,command,env):
    log=args.output/(name+'.log')
    with log.open('w') as stream:
        result=subprocess.run(command,cwd=SOURCE,env=env,stdout=stream,stderr=subprocess.STDOUT)
    record={'command':command,'exit_code':result.returncode,'log_sha256':sha(log)}
    (args.output/(name+'.status.json')).write_text(json.dumps(record,indent=2)+'\n')
    if result.returncode: raise SystemExit(f'{name} failed with exit {result.returncode}; see {log}')

inventory=json.loads((PROOF/'audit/source-inventory.json').read_text())
if inventory['source_commit']!=SCOPE['source_commit']:
    raise SystemExit('pinned native source pins disagree')
for record in inventory['files']:
    if sha(SOURCE/record['path'])!=record['sha256']:
        raise SystemExit('native source drift: '+record['path'])
for path,expected in SCOPE['source_build_inputs_sha256'].items():
    if sha(SOURCE/path)!=expected: raise SystemExit('native build input drift: '+path)
for name,binary in [('charon',args.charon),('aeneas',args.aeneas)]:
    if not binary.is_file(): raise SystemExit(f'missing pinned {name} binary: {binary}')
    directory=binary.resolve().parent
    head=subprocess.check_output(['git','-C',str(directory),'rev-parse','HEAD'],text=True).strip()
    if head!=PINS[name]: raise SystemExit(f'{name} source pin mismatch: {head}')
    if subprocess.run(['git','-C',str(directory),'diff','--quiet','HEAD']).returncode:
        raise SystemExit(name+' tracked source is dirty')
env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_BUILD_JOBS='1',
         CARGO_TARGET_DIR=str(PROOF/'tooling/workmeter-charon-target'))
llbc=args.output/'workmeter.llbc'
command=[str(args.charon),'cargo','--preset=aeneas','--sysroot=default','--dest-file='+str(llbc)]
command += ['--start-from=bulksketch::types::_::'+method for method in ['new','charge','used']]
command += ['--','--manifest-path',str(SOURCE/'Cargo.toml'),'-p','bulksketch','--lib','--locked']
logged('charon',command,env)
payload=json.loads(llbc.read_text())
if payload.get('has_errors') is not False: raise SystemExit('LLBC is incomplete: has_errors is not false')
lean=args.output/'lean';lean.mkdir(exist_ok=True)
logged('aeneas',[str(args.aeneas),'-backend','lean','-split-files','-dest',str(lean),str(llbc)],env)
record={'source_commit':SCOPE['source_commit'],
        'running_checkout_commit':subprocess.check_output(['git','-C',str(SOURCE),'rev-parse','HEAD'],text=True).strip(),
        'native_source_fingerprints_checked':len(inventory['files']),
        'charon_pin':PINS['charon'],'aeneas_pin':PINS['aeneas'],
        'llbc_sha256':sha(llbc),'llbc_has_errors':False,
        'generated':{p.name:sha(p) for p in sorted(lean.glob('*.lean'))},
        'implementation_proof_credit':0}
(args.output/'linkage.json').write_text(json.dumps(record,indent=2)+'\n')
print('Actual new/charge/used generated successfully; proof and axiom audit are separate gates.')
