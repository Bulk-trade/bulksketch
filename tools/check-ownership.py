#!/usr/bin/env python3
"""Check that the borrow checker rejects programs that misuse a decode job and its scratch arena.

Each fixture is compiled with rustc against the real crate sources (the private request
contract in src/sketch/contract.rs) and must fail with a borrow error."""
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PREFIX = (ROOT / 'src/lib.rs').read_text()
COMMON = '''
use sketch::contract::{RequestDecoder, RequestExecution};
fn forbidden<D: RequestDecoder<Gf64>>(decoder: &D, request: DecodeRequest<'_,Gf64>, arena: &mut DecodeScratch<Gf64>) {
'''
FIXTURES = {
    'two-live-jobs': '''
let mut first = decoder.new_job(request, arena).unwrap();
let mut second = decoder.new_job(request, arena).unwrap();
first.run_next(); second.run_next();
}
''',
    'swap-between-stages': '''
let mut job = decoder.new_job(request, arena).unwrap();
let layout = ScratchLayout::for_plan(&DecodePlan::v2(), &[1], &[Some(0)], 0, 0).unwrap();
let mut replacement = DecodeScratch::new(&layout).unwrap();
std::mem::swap(arena, &mut replacement);
job.run_next();
}
''',
    'reuse-while-report-live': '''
let report = decoder.new_job(request, arena).unwrap().finish().unwrap();
let _second = decoder.new_job(request, arena).unwrap();
std::hint::black_box(report.bucket_count());
}
''',
}


def main():
    # Place the generated crate root beside lib.rs so Rust resolves the real modules.
    accepted = []
    with tempfile.TemporaryDirectory(prefix="ownership-") as out:
        with tempfile.NamedTemporaryFile(mode='w', suffix='.rs', prefix="ownership_check_", dir=ROOT / 'src') as source:
            for name, body in FIXTURES.items():
                source.seek(0)
                source.truncate()
                source.write(PREFIX + '\n' + COMMON + body)
                source.flush()
                result = subprocess.run(['rustc', '--edition=2024', '--crate-type=lib', '--emit=metadata',
                    '--crate-name=ownership_check', '--out-dir', out, source.name], text=True,
                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                if result.returncode == 0:
                    accepted.append(name)
                    print(f'{name}: forbidden ownership program was ACCEPTED')
                else:
                    assert 'error[E0499]' in result.stdout or 'error[E0502]' in result.stdout, result.stdout
                    print(f'{name}: rejected by borrow checker')
    assert not accepted, f'forbidden ownership programs were accepted: {accepted}'


if __name__ == '__main__':
    main()
