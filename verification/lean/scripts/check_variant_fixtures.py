#!/usr/bin/env python3
"""Exercise actual translator-policy AST gates without mutating production inputs.

This isolates the receipt and per-refinement gates from verify_bridge.main.
The full verifier separately checks frozen inputs, source bodies and proof terms.
"""
from pathlib import Path
import ast
import copy
import hashlib
import json
import re
import subprocess
import tempfile
ROOT=Path(__file__).resolve().parents[1]
source=(ROOT/'scripts/verify_bridge.py').read_text();tree=ast.parse(source)
main=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='main')
loop=next(n for n in main.body if isinstance(n,ast.For) and isinstance(n.target,ast.Name) and n.target.id=='variant')
code=compile(ast.fix_missing_locations(ast.Module(body=[loop],type_ignores=[])),'actual-verify-bridge-variant-gates','exec')
link=json.loads((ROOT/'bridge/source-linkage.json').read_text());variant=link['reviewed_translator_variants'][0];original=json.loads((ROOT/variant['receipt']).read_text());runtime=ROOT/'tooling/aeneas'
runtime_head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=runtime,text=True).strip()
def run(name,args,timeout,cwd):
 r=subprocess.run(args,cwd=cwd,capture_output=True,text=True,timeout=timeout)
 if r.returncode:raise RuntimeError(r.stdout+r.stderr)
 return {'name':name,'exit_code':0},r.stdout
cases=[
 ('positive',lambda d,v:None),
 ('omit-checks-command',lambda d,v:d['extraction']['command'].remove('-checks')),
 ('omit-checks-contract',lambda d,v:d['extraction']['required_flags'].remove('-checks')),
 ('wrong-base',lambda d,v:d.update(base_aeneas_commit='wrong')),
 ('wrong-patch-hash',lambda d,v:v.update(patch_sha256='wrong')),
 ('omit-modified-source',lambda d,v:d['modified_sources'].pop('src/interp/InterpJoin.ml')),
 ('omit-regression',lambda d,v:d['regressions'].pop()),
 ('unchecked-accepted',lambda d,v:next(x for x in d['regressions'] if x['case']=='without-checks').update(exit_code=0)),
 ('wrong-original-llbc-hash',lambda d,v:d['extraction'].update(input_sha256='wrong')),
 ('wrong-canonical-input',lambda d,v:d['extraction'].update(input='extraction/canonical-arithmetic/maps/arithmetic.llbc', input_sha256=hashlib.sha256((ROOT/'extraction/canonical-arithmetic/maps/arithmetic.llbc').read_bytes()).hexdigest())),
 ('omit-generated-artifacts',lambda d,v:d['extraction'].update(generated=[])),
 ('missing-generated-artifact',lambda d,v:d['extraction']['generated'].pop()),
 ('duplicated-generated-artifact',lambda d,v:d['extraction']['generated'].__setitem__(1,copy.deepcopy(d['extraction']['generated'][0]))),
 ('extra-generated-artifact',lambda d,v:d['extraction']['generated'].append(copy.deepcopy(d['extraction']['generated'][0])))]
results=[]
for name,mutate in cases:
 with tempfile.TemporaryDirectory() as t:
  shadow=Path(t);(shadow/'tooling/aeneas-loop-capture').mkdir(parents=True)
  (shadow/'extraction').symlink_to(ROOT/'extraction',target_is_directory=True)
  (shadow/variant['patch']).write_bytes((ROOT/variant['patch']).read_bytes())
  d=copy.deepcopy(original);v=copy.deepcopy(variant);mutate(d,v)
  (shadow/variant['receipt']).write_text(json.dumps(d))
  env=dict(ROOT=shadow,variants=[v],runtime=runtime,runtime_head=runtime_head,linkage=link,records=[],sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest(),run=run,re=re,json=json)
  try:exec(code,env);status='accepted'
  except (RuntimeError,KeyError,ValueError) as e:status='rejected';reason=str(e)
  results.append({'case':name,'status':status});print(name,status)

# Exercise the exact per-refinement attribution statements from the same main AST.
refine_loop=next(n for n in main.body if isinstance(n,ast.For) and isinstance(n.target,ast.Tuple) and any(isinstance(x,ast.Name) and x.id=='native_id' for x in n.target.elts))
assignment=next(n for n in refine_loop.body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='used_variants' for x in n.targets))
attribution_if=next(n for n in refine_loop.body if isinstance(n,ast.If) and 'source refinement hides or lacks its translator variant' in ast.unparse(n))
attribution_code=compile(ast.fix_missing_locations(ast.Module(body=[assignment,attribution_if],type_ignores=[])),'actual-verify-bridge-refinement-attribution','exec')
registry=json.loads((ROOT/'bridge/obligations.json').read_text());active=next(x for x in registry['refinements'] if x['generated_declaration']=='bulksketch.field.maps.inverse');plain=next(x for x in registry['refinements'] if x['generated_declaration']=='bulksketch.field.gf64.mul')
attribution_cases=[('valid-patched',active,lambda e,p:None),
 ('valid-pinned',plain,lambda e,p:None),
 ('hidden-entry-variant',active,lambda e,p:e.pop('translator_variant')),
 ('hidden-projection-variant',active,lambda e,p:[x.pop('translator_variant',None) for x in p]),('unknown-variant',active,lambda e,p:(e.update(translator_variant='unknown'),[x.update(translator_variant='unknown') for x in p if x.get('translator_variant')]))]
for name,entry,mutate in attribution_cases:
 e=copy.deepcopy(entry);p=copy.deepcopy(link['native_generated_projections']);mutate(e,p)
 try:exec(attribution_code,dict(entry=e,projections=p,variant_ids={x['id'] for x in link['reviewed_translator_variants']}));status='accepted'
 except RuntimeError:status='rejected'
 results.append({'case':name,'status':status});print(name,status)

for row in results:
 expected = 'accepted' if row['case'] in {'positive','valid-patched','valid-pinned'} else 'rejected'
 if row['status'] != expected:
  raise RuntimeError('variant/attribution gate outcome differs: '+row['case'])
print('all 19 gate/attribution checks passed')
summary = {"status": "passed", "valid_cases": 3, "negative_cases": 16,
           "cases": results, "production_inputs_modified": False}
output = ROOT / "bridge/audit/results/variant-fixtures.json"
output.parent.mkdir(parents=True, exist_ok=True)
output.write_text(json.dumps(summary, indent=2) + "\n")
