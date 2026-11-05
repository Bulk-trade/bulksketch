#!/usr/bin/env python3
"""Fetch only exact Lean dependency commits already pinned by Aeneas's manifest."""
import json
from pathlib import Path
import subprocess

ROOT=Path(__file__).resolve().parents[1]
RUNTIME=ROOT/'tooling/aeneas/backends/lean'
WORKSPACE=ROOT/'bridge'
(ROOT/'tooling/logs').mkdir(parents=True,exist_ok=True)
manifest=json.loads((RUNTIME/'lake-manifest.json').read_text())
records=[]
with (ROOT/'tooling/logs/lean-runtime-source-fetch.log').open('w') as log:
    for package in manifest['packages']:
        if package['type']!='git': raise SystemExit('unexpected non-Git dependency')
        destination=WORKSPACE/manifest['packagesDir']/package['name']
        destination.mkdir(parents=True,exist_ok=True)
        if not (destination/'.git').exists():
            subprocess.run(['git','init','--quiet',str(destination)],check=True,stdout=log,stderr=log)
            subprocess.run(['git','-C',str(destination),'remote','add','origin',package['url']],check=True,stdout=log,stderr=log)
        if subprocess.run(['git','-C',str(destination),'cat-file','-e',package['rev']+'^{commit}'],stdout=log,stderr=log).returncode:
            subprocess.run(['git','-C',str(destination),'fetch','--depth','1','--filter=blob:none','origin',package['rev']],check=True,stdout=log,stderr=log)
        subprocess.run(['git','-C',str(destination),'checkout','--detach',package['rev']],check=True,stdout=log,stderr=log)
        actual=subprocess.check_output(['git','-C',str(destination),'rev-parse','HEAD'],text=True).strip()
        if actual!=package['rev']: raise SystemExit('dependency commit mismatch')
        records.append({'name':package['name'],'url':package['url'],'commit':actual})
        print(package['name'],actual,flush=True)
(ROOT/'tooling/lean-runtime-source-pins.json').write_text(json.dumps(records,indent=2)+'\n')
