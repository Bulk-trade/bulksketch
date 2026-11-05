#!/usr/bin/env python3
"""Fetch artifacts only for explicit Mathlib imports in runtime and native proofs."""
import json
import os
from pathlib import Path
import re
import subprocess

ROOT=Path(__file__).resolve().parents[1]
RUNTIME=ROOT/'tooling/aeneas/backends/lean'
WORKSPACE=ROOT/'bridge'
(ROOT/'tooling/logs').mkdir(parents=True,exist_ok=True)
modules=set()
for directory in [RUNTIME/'Aeneas',RUNTIME/'AeneasMeta',WORKSPACE/'BulksketchBridge']:
    for source in directory.rglob('*.lean'):
        for line in source.read_text().splitlines():
            match=re.match(r'^(?:public\s+)?import\s+(Mathlib\.[A-Za-z0-9_.]+)',line)
            if match: modules.add(match.group(1))
command=['lake','+leanprover/lean4:v4.35.0','exe','cache','get',*sorted(modules)]
env=dict(os.environ, LEAN_NUM_THREADS='2', CI='1', MATHLIB_NO_CACHE_ON_UPDATE='1')
with (ROOT/'tooling/logs/lean-runtime-cache.log').open('w') as log:
    result=subprocess.run(command,cwd=WORKSPACE,env=env,stdout=log,stderr=subprocess.STDOUT)
record={'command':command,'cwd':str(WORKSPACE),'exit_code':result.returncode,
        'explicit_mathlib_roots':sorted(modules),'preserve_pinned_lake_manifest':True}
(ROOT/'tooling/lean-runtime-cache.status.json').write_text(json.dumps(record,indent=2)+'\n')
print('targeted Mathlib cache exit',result.returncode,flush=True)
raise SystemExit(result.returncode)
