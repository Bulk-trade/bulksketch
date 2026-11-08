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
import runpy
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

dense = next(item for item in link["reviewed_translator_variants"]
             if item["id"] == "checked-shared-expansion-owner-v1")
dense_original = json.loads((ROOT / dense["receipt"]).read_text())
dense_check = next(node for node in tree.body if isinstance(node, ast.FunctionDef)
                   and node.name == "check_dense_prefix_variant")
dense_code = compile(ast.fix_missing_locations(ast.Module(body=[dense_check, loop], type_ignores=[])),
                     "actual-verify-bridge-dense-prefix-gate", "exec")
dense_cases = [
    ("dense-positive", lambda receipt, _: None),
    ("dense-missing-checks", lambda receipt, _: receipt["extraction"]["command"].remove("-checks")),
    ("dense-missing-sequential", lambda receipt, _: receipt["extraction"]["required_flags"].remove("-sequential")),
    ("dense-missing-child-control", lambda receipt, _: receipt["regressions"].pop()),
    ("dense-wrong-input", lambda receipt, _: receipt["extraction"].update(input="other.llbc")),
    ("dense-extra-patch-file", lambda receipt, _: receipt["modified_sources"].update(other="bogus")),
    ("dense-missing-guard-source", lambda receipt, _: receipt["regression_sources"].pop(
        "tooling/aeneas-dense-prefix/guards/dense_prefix_guards.ml")),
    ("dense-incorrect-guard-source", lambda receipt, _: receipt["regression_sources"].update({
        "tooling/aeneas-dense-prefix/guards/dense_prefix_guards.ml": "bad"})),
    ("dense-value-controls-failed", lambda receipt, _: next(item for item in receipt["commands"]
        if item["name"] == "rust-value-regressions").update(exit_code=1)),
    ("dense-claim-source-credit-from-controls", lambda receipt, _: receipt.update(
        new_native_coverage_credit_from_tests=1)),
    ("unknown-translator-id", lambda _, entry: entry.update(id="unknown")),
]
for name, mutate in dense_cases:
    receipt, entry = copy.deepcopy(dense_original), copy.deepcopy(dense)
    mutate(receipt, entry)
    with tempfile.TemporaryDirectory() as temp:
        shadow = Path(temp)
        (shadow / "extraction").symlink_to(ROOT / "extraction", target_is_directory=True)
        for rel in set(dense_original["regression_sources"]) | {dense["patch"]}:
            dest = shadow / rel
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.symlink_to(ROOT / rel)
        (shadow / dense["receipt"]).write_text(json.dumps(receipt))
        env = dict(ROOT=shadow, variants=[entry], runtime=runtime, runtime_head=runtime_head,
                   linkage=link, records=[], sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest(),
                   run=run, re=re, json=json)
        try:
            exec(dense_code, env)
            status = "accepted"
        except (RuntimeError, KeyError, ValueError):
            status = "rejected"
    results.append({"case": name, "status": status})
    print(name, status)

dense_mul = next(item for item in link["reviewed_translator_variants"]
                 if item["id"] == "checked-shared-loop-erasure-v1")
mul_original = json.loads((ROOT / dense_mul["receipt"]).read_text())
mul_check = next(node for node in tree.body if isinstance(node, ast.FunctionDef)
                 and node.name == "check_dense_mul_variant")
mul_code = compile(ast.fix_missing_locations(ast.Module(body=[mul_check, loop], type_ignores=[])),
                   "actual-verify-bridge-dense-mul-gate", "exec")
mul_cases = [
    ("dense-mul-positive", lambda receipt: None),
    ("dense-mul-wrong-parent", lambda receipt: receipt.update(parent_patch_sha256="wrong")),
    ("dense-mul-wrong-baseline", lambda receipt: receipt.update(baseline_binary_sha256="wrong")),
    ("dense-mul-omits-checks", lambda receipt: receipt["extraction"]["command"].remove("-checks")),
    ("dense-mul-missing-mutable-control", lambda receipt: receipt["regressions"].__setitem__(
        slice(None), [item for item in receipt["regressions"] if item["case"] != "mutable-given-back-payload"])),
    ("dense-mul-unchecked-accepted", lambda receipt: next(item for item in receipt["commands"]
        if item["name"] == "without-checks").update(exit_code=0)),
    ("dense-mul-square-control-failed", lambda receipt: next(item for item in receipt["commands"]
        if item["name"] == "square-control").update(exit_code=1)),
    ("dense-mul-wrong-generated-hash", lambda receipt: receipt["extraction"]["generated"][1].update(sha256="wrong")),
]
for name, mutate in mul_cases:
    receipt = copy.deepcopy(mul_original)
    mutate(receipt)
    with tempfile.TemporaryDirectory() as temp:
        shadow = Path(temp)
        (shadow / "extraction").symlink_to(ROOT / "extraction", target_is_directory=True)
        (shadow / "tooling").mkdir()
        (shadow / "tooling/aeneas-dense-prefix").symlink_to(
            ROOT / "tooling/aeneas-dense-prefix", target_is_directory=True)
        for rel in set(mul_original["regression_sources"]) | {dense_mul["patch"]}:
            dest = shadow / rel
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.symlink_to(ROOT / rel)
        (shadow / dense_mul["receipt"]).write_text(json.dumps(receipt))
        env = dict(ROOT=shadow, variants=[dense_mul], runtime=runtime, runtime_head=runtime_head,
                   linkage=link, records=[], sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest(),
                   run=run, re=re, json=json)
        try:
            exec(mul_code, env)
            status = "accepted"
        except (RuntimeError, KeyError, ValueError):
            status = "rejected"
    results.append({"case": name, "status": status})
    print(name, status)

horner = next(item for item in link["reviewed_translator_variants"]
              if item["id"] == "checked-ended-shared-scalar-v1")
horner_original = json.loads((ROOT / horner["receipt"]).read_text())
horner_check = next(node for node in tree.body if isinstance(node, ast.FunctionDef)
                    and node.name == "check_horner_match_variant")
horner_code = compile(ast.fix_missing_locations(ast.Module(body=[horner_check, loop], type_ignores=[])),
                      "actual-verify-bridge-horner-matcher-gate", "exec")
horner_cases = [
    ("horner-positive", lambda receipt: None),
    ("horner-omits-checks", lambda receipt: receipt["extraction"]["command"].remove("-checks")),
    ("horner-missing-child-control", lambda receipt: receipt["regressions"].remove(
        next(item for item in receipt["regressions"] if item["case"] == "distinct-child-payload"))),
    ("horner-unchecked-accepted", lambda receipt: next(item for item in receipt["commands"]
        if item["name"] == "fixture-without-checks").update(exit_code=0)),
    ("horner-omits-external-template", lambda receipt: receipt["extraction"]["generated"].pop()),
    ("horner-extra-translator-source", lambda receipt: receipt["modified_sources"].update(other="wrong")),
]
for name, mutate in horner_cases:
    receipt = copy.deepcopy(horner_original)
    mutate(receipt)
    with tempfile.TemporaryDirectory() as temp:
        shadow = Path(temp)
        (shadow / "extraction").symlink_to(ROOT / "extraction", target_is_directory=True)
        for rel in set(horner_original["regression_sources"]) | {horner["patch"]}:
            dest = shadow / rel
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.symlink_to(ROOT / rel)
        (shadow / horner["receipt"]).write_text(json.dumps(receipt))
        env = dict(ROOT=shadow, variants=[horner], runtime=runtime, runtime_head=runtime_head,
                   linkage=link, records=[], sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest(),
                   run=run, re=re, json=json)
        try:
            exec(horner_code, env)
            status = "accepted"
        except (RuntimeError, KeyError, ValueError):
            status = "rejected"
    results.append({"case": name, "status": status})
    print(name, status)

pclmul = link["reviewed_pclmul_horner_extensions"][0]
pclmul_original = json.loads((ROOT / pclmul["receipt"]).read_text())
pclmul_check = runpy.run_path(str(ROOT / "scripts/verify_bridge.py"))["check_pclmul_horner_extension"]
pclmul_cases = [
    ("pclmul-horner-positive", lambda receipt, variants: None),
    ("pclmul-horner-omits-checks", lambda receipt, variants: receipt["checked_extraction"]["command"].remove("-checks")),
    ("pclmul-horner-wrong-patch", lambda receipt, variants: receipt.update(variant_patch_sha256="wrong")),
    ("pclmul-horner-unreviewed", lambda receipt, variants: variants.clear()),
    ("pclmul-horner-unchecked-accepted", lambda receipt, variants: receipt["rejections"]["unchecked"].update(exit_code=0)),
    ("pclmul-horner-missing-type-artifact", lambda receipt, variants: receipt["checked_extraction"]["generated"].pop()),
    ("pclmul-horner-short-replay", lambda receipt, variants: receipt["replay"].update(exact_generated_artifacts=3)),
]
for name, mutate in pclmul_cases:
    receipt = copy.deepcopy(pclmul_original)
    variants = copy.deepcopy(link["reviewed_translator_variants"])
    mutate(receipt, variants)
    try:
        pclmul_check(pclmul, receipt, variants, runtime_head, link)
        status = "accepted"
    except (RuntimeError, KeyError, ValueError):
        status = "rejected"
    results.append({"case": name, "status": status})
    print(name, status)

certificate = next(entry for entry in link["reviewed_translator_variants"]
                   if entry["id"] == "checked-ended-projector-leaf-v1")
certificate_original = json.loads((ROOT / certificate["receipt"]).read_text())
certificate_check = runpy.run_path(str(ROOT / "scripts/verify_bridge.py"))["check_certificate_match_variant"]
certificate_cases = [
    ("certificate-positive", lambda receipt: None),
    ("certificate-omits-checks", lambda receipt: receipt["extraction"]["command"].remove("-checks")),
    ("certificate-extra-source", lambda receipt: receipt["modified_sources"].update(other="wrong")),
    ("certificate-missing-output", lambda receipt: receipt["extraction"]["generated"].pop()),
    ("certificate-pinned-accepted", lambda receipt: receipt["pinned_rejection"].update(exit_code=0)),
    ("certificate-missing-child-control", lambda receipt: receipt["regressions"].pop(4)),
]
for name, mutate in certificate_cases:
    receipt = copy.deepcopy(certificate_original)
    mutate(receipt)
    try:
        certificate_check(certificate, receipt, runtime, runtime_head, link)
        status = "accepted"
    except (RuntimeError, KeyError, ValueError):
        status = "rejected"
    results.append({"case": name, "status": status})
    print(name, status)

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
dense_square = next(entry for entry in registry["refinements"]
                    if entry["generated_declaration"] == "bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial.square_into")
attribution_cases.extend([
    ("valid-dense-source", dense_square, lambda entry, projections: None),
    ("wrong-dense-source-variant", dense_square,
     lambda entry, projections: entry.update(translator_variant="checked-frozen-capture-v1")),
])
for name,entry,mutate in attribution_cases:
 e=copy.deepcopy(entry);p=copy.deepcopy(link['native_generated_projections']);mutate(e,p)
 try:exec(attribution_code,dict(entry=e,projections=p,variant_ids={x['id'] for x in link['reviewed_translator_variants']}));status='accepted'
 except RuntimeError:status='rejected'
 results.append({'case':name,'status':status});print(name,status)

for row in results:
 expected = 'accepted' if row['case'] in {'positive','dense-positive','dense-mul-positive','horner-positive','pclmul-horner-positive','certificate-positive','valid-patched','valid-pinned','valid-dense-source'} else 'rejected'
 if row['status'] != expected:
  raise RuntimeError('variant/attribution gate outcome differs: '+row['case'])
valid_count = sum(row["status"] == "accepted" for row in results)
print(f"all {len(results)} gate/attribution checks passed")
summary = {"status": "passed", "valid_cases": valid_count, "negative_cases": len(results) - valid_count,
           "cases": results, "production_inputs_modified": False}
output = ROOT / "bridge/audit/results/variant-fixtures.json"
output.parent.mkdir(parents=True, exist_ok=True)
output.write_text(json.dumps(summary, indent=2) + "\n")
