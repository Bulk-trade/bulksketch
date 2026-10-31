//! Decode time of `bulksketch` against minisketch impl 0 (portable) and impl 1 (CLMUL).
//!
//! Each case is a request of one or more rows (buckets) of one capacity. Both
//! libraries get the same inputs: a local sketch built ahead of time and the
//! remote side's serialized row bytes. Per row, bulksketch XORs, decodes and
//! verifies inside one `decode_rows_into` call; minisketch deserializes the remote
//! bytes into a reused sketch, merges the local sketch and decodes with an output
//! buffer of the full capacity. Every case cycles through a pool of distinct
//! fixtures so that no single input is timed over and over.
//!
//! Run: `cargo bench -p bulksketch-oracle --bench decode`. Pin the process to one
//! core for steadier numbers, e.g. `taskset -c 2 cargo bench ...` on Linux.

use {
    bulksketch::{DecodeRow, FrozenSketch, Gf64},
    bulksketch_oracle::{
        BulkDecoder, Row, bulk_row, ids, minisketch, minisketch_bytes, mix, payload,
        symmetric_difference,
    },
    criterion::{BenchmarkId, Criterion, criterion_group, criterion_main},
    minisketch_rs::Minisketch,
    std::hint::black_box,
};

const POOL: usize = 32;
const SHARED: usize = 32;

struct Case {
    name: String,
    capacity: usize,
    rows: usize,
    /// Size of the symmetric difference in each row, for fixture `index`.
    degrees: Box<dyn Fn(usize) -> Vec<usize>>,
}

/// A 16-bucket vote with 10 to 12 differences in total, routed to buckets by
/// `id % 16`, so most rows hold 0 to 2 differences and some are equal.
fn spread(index: usize) -> Vec<usize> {
    let mut rows = vec![0; 16];
    for j in 0..10 + index % 3 {
        rows[(mix((index as u64) << 8 | j as u64) % 16) as usize] += 1;
    }
    rows
}

fn cases() -> Vec<Case> {
    let mut cases = Vec::new();
    for capacity in [18, 89] {
        cases.push(Case {
            name: format!("vote_16x{capacity}_total11"),
            capacity,
            rows: 16,
            degrees: Box::new(spread),
        });
    }
    for capacity in [18, 89] {
        cases.push(Case {
            name: format!("vote_16x{capacity}_d11"),
            capacity,
            rows: 16,
            degrees: Box::new(|_| vec![11; 16]),
        });
    }
    for capacity in [18, 89] {
        for d in [1, 2, 5] {
            cases.push(Case {
                name: format!("row_c{capacity}_d{d}"),
                capacity,
                rows: 1,
                degrees: Box::new(move |_| vec![d]),
            });
        }
    }
    // Pressure-like: half of the rows within capacity, half beyond it (these fail).
    cases.push(Case {
        name: "pressure_16x18".into(),
        capacity: 18,
        rows: 16,
        degrees: Box::new(|_| vec![6, 8, 10, 12, 14, 16, 17, 18, 19, 20, 24, 28, 32, 40, 48, 60]),
    });
    cases
}

struct Fixture {
    degrees: Vec<usize>,
    locals: Vec<FrozenSketch<Gf64>>,
    local_sets: Vec<Vec<u64>>,
    remotes: Vec<Vec<u8>>,
    truths: Vec<Vec<u64>>,
}

fn fixture(case: &Case, index: usize) -> Fixture {
    let mut f = Fixture {
        degrees: (case.degrees)(index),
        locals: Vec::new(),
        local_sets: Vec::new(),
        remotes: Vec::new(),
        truths: Vec::new(),
    };
    assert_eq!(f.degrees.len(), case.rows);
    for (row, &d) in f.degrees.clone().iter().enumerate() {
        let stream = (index as u64) << 40 | (row as u64) << 32 | case.capacity as u64;
        let shared = ids(stream ^ 0xabcd, SHARED);
        let diff = ids(stream, d);
        let mut local = shared.clone();
        let mut remote = shared;
        for (i, &id) in diff.iter().enumerate() {
            if i % 2 == 0 {
                local.push(id);
            } else {
                remote.push(id);
            }
        }
        let remote_bytes = payload(&bulk_row(case.capacity, &remote)).to_vec();
        assert_eq!(
            remote_bytes,
            minisketch_bytes(&minisketch(0, case.capacity, &remote).unwrap()),
            "row bytes are minisketch bytes"
        );
        f.truths.push(symmetric_difference(&local, &remote));
        f.locals.push(bulk_row(case.capacity, &local));
        f.local_sets.push(local);
        f.remotes.push(remote_bytes);
    }
    f
}

fn minisketch_count(
    work: &mut Minisketch,
    local: &Minisketch,
    remote: &[u8],
    out: &mut [u64],
) -> usize {
    work.deserialize(remote);
    work.merge(local).unwrap();
    work.decode(out).unwrap_or(0)
}

fn bench(c: &mut Criterion) {
    for case in cases() {
        let fixtures: Vec<_> = (0..POOL).map(|i| fixture(&case, i)).collect();
        let rows: Vec<Vec<DecodeRow<'_, Gf64>>> = fixtures
            .iter()
            .map(|f| {
                f.locals
                    .iter()
                    .zip(&f.remotes)
                    .map(|(local, remote)| DecodeRow {
                        local,
                        remote,
                        candidates: &[],
                    })
                    .collect()
            })
            .collect();
        let mut decoder = BulkDecoder::new(case.capacity, case.rows);

        // Check results once before timing: rows within capacity decode to the
        // true difference in both libraries (equal rows report Equal in
        // bulksketch); rows beyond it fail in bulksketch.
        for (f, rows) in fixtures.iter().zip(&rows) {
            for ((row, truth), &d) in decoder.decode(rows).iter().zip(&f.truths).zip(&f.degrees) {
                if d == 0 {
                    assert_eq!(row, &Row::Equal, "{}", case.name);
                } else if d <= case.capacity {
                    assert_eq!(row, &Row::Decoded(truth.clone()), "{}", case.name);
                } else {
                    assert_eq!(row, &Row::Failed, "{}", case.name);
                }
            }
        }

        let mut group = c.benchmark_group(case.name.as_str());
        let mut k = 0;
        group.bench_function(BenchmarkId::from_parameter("bulksketch"), |b| {
            b.iter(|| {
                k = (k + 1) % POOL;
                black_box(decoder.decode_count(black_box(&rows[k])))
            });
        });

        for implementation in [0, 1] {
            let Some(mut work) = minisketch(implementation, case.capacity, &[]) else {
                eprintln!(
                    "{}: minisketch impl {implementation} unavailable, skipped",
                    case.name
                );
                continue;
            };
            let locals: Vec<Vec<Minisketch>> = fixtures
                .iter()
                .map(|f| {
                    f.local_sets
                        .iter()
                        .map(|set| minisketch(implementation, case.capacity, set).unwrap())
                        .collect()
                })
                .collect();
            let mut out = vec![0; case.capacity];
            for (f, locals) in fixtures.iter().zip(&locals) {
                for ((local, remote), (truth, &d)) in locals
                    .iter()
                    .zip(&f.remotes)
                    .zip(f.truths.iter().zip(&f.degrees))
                {
                    if d <= case.capacity {
                        let n = minisketch_count(&mut work, local, remote, &mut out);
                        let mut got = out[..n].to_vec();
                        got.sort_unstable();
                        assert_eq!(&got, truth, "{} impl {implementation}", case.name);
                    }
                }
            }
            let name = format!("minisketch-impl{implementation}");
            group.bench_function(BenchmarkId::from_parameter(name), |b| {
                b.iter(|| {
                    k = (k + 1) % POOL;
                    let mut total = 0;
                    for (local, remote) in locals[k].iter().zip(&fixtures[k].remotes) {
                        total += minisketch_count(&mut work, local, black_box(remote), &mut out);
                    }
                    black_box(total)
                });
            });
        }
        group.finish();
    }
}

criterion_group!(benches, bench);
criterion_main!(benches);
