#![forbid(unsafe_code)]

use {
    super::*,
    crate::{
        BackendId,
        backend::{contract::BulkKernels, portable::Portable},
        decode::{
            row::{RowBudget, RowDecoder, RowExecution, RowInput, RowResult},
            stages::BinaryDecoder,
        },
        field::{
            BinaryField, reference,
            tiny::{Gf4, Gf16},
        },
        types::WorkMeter,
    },
    std::collections::BTreeSet,
};

fn mix(mut value: u64) -> u64 {
    value = value.wrapping_add(0x9e37_79b9_7f4a_7c15);
    value = (value ^ (value >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    value = (value ^ (value >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    value ^ (value >> 31)
}

fn tiny<F: BinaryField>(
    words: &[u64],
    beta: usize,
    zero: bool,
    hints: &[u64],
    v2: bool,
    seed: u64,
) -> Outcome {
    let Some(nonzero) = beta.checked_sub(usize::from(zero)) else {
        return Outcome::Failed(DecodeFailure::DegreeExceedsBudget);
    };
    let plan = if v2 {
        DecodePlan::v2()
    } else {
        DecodePlan::v1()
    };
    let (bound, layout) = plan
        .complete_bound(
            &[u16::try_from(words.len()).unwrap()],
            &[Some(nonzero)],
            beta,
            hints.len(),
        )
        .unwrap();
    let mut scratch = DecodeScratch::<F>::new(&layout).unwrap();
    scratch.words.fill(F::MASK);
    let (mut workspace, _) = scratch.split(&layout);
    let row_layout = RowLayout::new(words.len(), nonzero).unwrap();
    let (_, _, mut row) = workspace.row(&row_layout);
    let input = RowInput {
        difference: words,
        candidates: hints,
    };
    let mut execution = <BinaryDecoder as RowDecoder<F, Portable>>::begin(RowBudget {
        nonzero,
        total: beta,
    });
    execution.set_splitter_seed(seed);
    if v2 {
        execution.start_probes(words);
    }
    let mut meter = WorkMeter::new(bound);
    match execution.finish(input, &mut row, &mut meter).unwrap() {
        RowResult::Equal => Outcome::Equal,
        RowResult::Failed(reason) => Outcome::Failed(reason),
        RowResult::Decoded(roots) => {
            let mut ids = Vec::new();
            if zero {
                ids.push(0);
            }
            ids.extend_from_slice(roots);
            Outcome::Decoded(ids)
        }
    }
}

fn tiny_corpus() -> (usize, usize) {
    let mut arbitrary = 0;
    for c in 1..=3 {
        for code in 0..1usize << (2 * c) {
            let words: Vec<_> = (0..c)
                .map(|i| u64::try_from((code >> (2 * i)) & 3).unwrap())
                .collect();
            for beta in 0..=c {
                for zero in [false, true] {
                    for hints in [&[][..], &[2][..], &[1, 2, 3][..]] {
                        assert_eq!(
                            tiny::<Gf4>(&words, beta, zero, hints, true, 1),
                            tiny::<Gf4>(&words, beta, zero, hints, false, 1),
                            "arbitrary GF4 row {words:?} beta={beta} zero={zero}"
                        );
                        arbitrary += 1;
                    }
                }
            }
        }
    }
    let mut exhaustive = 0;
    for mask in 0..65536u32 {
        let roots: Vec<_> = (1..16).filter(|id| mask & (1 << id) != 0).collect();
        let mut words = [0; 3];
        <Portable as BulkKernels<Gf16>>::insert_nonzero(&mut words, &roots);
        let zero = mask & 1 != 0;
        for beta in 0..=3 {
            let hints = if mask % 3 == 0 { &[][..] } else { &roots };
            let v1 = tiny::<Gf16>(&words, beta, zero, hints, false, 0xd6e8_feb8_6659_fd93);
            let v2 = tiny::<Gf16>(&words, beta, zero, hints, true, 0xd6e8_feb8_6659_fd93);
            assert_eq!(v2, v1, "GF16 set mask={mask:#x}, beta={beta}");
            exhaustive += 1;
        }
    }
    (arbitrary, exhaustive)
}

fn gf64_corpus() -> usize {
    let mut paired = 0;
    for (buckets, c) in [(16, 18), (16, 32), (4, 72), (1, 89)] {
        for trial in 0..256usize {
            let beta = [c, c.min(64), c / 2, 1, 2, 0][(trial / 4) % 6];
            let protected_width = (2 * c - 2 * beta).max(1);
            let count = [
                0,
                1,
                2,
                beta,
                beta + 1,
                2 * c - beta,
                2 * c - beta + 1,
                beta / 2,
                beta + 1 + trial % protected_width,
            ][(trial / 24) % 9];
            let mut rows = vec![BTreeSet::new(); buckets];
            let mut index = u64::try_from(trial).unwrap() << 32;
            while rows.iter().any(|r| r.len() < count) {
                index += 1;
                let id = match trial % 4 {
                    0 => mix(index),
                    1 => mix(index) & 0x3fff,
                    2 => mix(index) >> 24,
                    _ => mix(index) >> 40,
                };
                let bucket = usize::try_from(id % u64::try_from(buckets).unwrap()).unwrap();
                if id != 0 && rows[bucket].len() < count {
                    rows[bucket].insert(id);
                }
            }
            let rows: Vec<Vec<u64>> = rows.into_iter().map(|r| r.into_iter().collect()).collect();
            let mut odd = vec![vec![0; c]; buckets];
            for (words, ids) in odd.iter_mut().zip(&rows) {
                <Portable as BulkKernels<Gf64>>::insert_nonzero(words, ids);
            }
            let slices: Vec<_> = odd.iter().map(Vec::as_slice).collect();
            let fixture = Fixture::new(&slices, false);
            let hints: Vec<_> = match trial % 3 {
                0 => vec![],
                1 => rows
                    .iter()
                    .flat_map(|r| r.iter().step_by(2))
                    .copied()
                    .chain([0, u64::MAX, u64::MAX])
                    .collect(),
                _ => rows.iter().flatten().copied().chain([0, 0]).collect(),
            };
            for seed in [1, 0xd6e8_feb8_6659_fd93, u64::MAX] {
                let v1 = fixture.run(DecodePlan::v1(), beta, &hints, seed);
                let v2 = fixture.run(DecodePlan::v2(), beta, &hints, seed);
                assert_eq!(
                    v2.rows, v1.rows,
                    "GF64 {buckets}x{c} trial={trial} d={count} beta={beta} seed={seed:#x}"
                );
                for ((outcome, actual_ids), words) in v2.rows.iter().zip(&rows).zip(&odd) {
                    if count <= beta {
                        assert_eq!(
                            *outcome,
                            if count == 0 {
                                Outcome::Equal
                            } else {
                                Outcome::Decoded(actual_ids.clone())
                            }
                        );
                    } else if count <= 2 * c - beta {
                        assert!(matches!(outcome, Outcome::Failed(_)), "protected overflow");
                    }
                    let ids = match outcome {
                        Outcome::Equal => &[][..],
                        Outcome::Decoded(ids) => ids,
                        Outcome::Failed(_) => continue,
                    };
                    let mut encoded = vec![0; c];
                    for &id in ids {
                        let square = reference::mul::<Gf64>(id, id);
                        let mut power = id;
                        for word in &mut encoded {
                            *word ^= power;
                            power = reference::mul::<Gf64>(power, square);
                        }
                    }
                    assert_eq!(
                        encoded, *words,
                        "independent full re-encoding on every accepted corpus row"
                    );
                }
                paired += 1;
            }
        }
    }
    paired
}

#[test]
fn v2_v1_equivalence() {
    success(&[1], 1, false, &[1], ONE, 13);
    success(&[3, 9], 2, false, &[1, 2], TWO, 212);
    let (arbitrary, exhaustive) = tiny_corpus();
    let paired = gf64_corpus();
    assert_eq!(
        Fixture::new(&[&[3]], false)
            .run(DecodePlan::v2(), 1, &[], 1)
            .rows,
        [Outcome::Decoded(vec![3])],
        "retained singleton alias of set {{1,2}}"
    );
    assert_eq!(
        Fixture::new(&[&[0]], false)
            .run(DecodePlan::v2(), 1, &[], 1)
            .rows,
        [Outcome::Equal],
        "retained Equal alias of {{1,2,3}}"
    );
    eprintln!(
        "V1/V2 differential: arbitrary GF4 comparisons={arbitrary}; exhaustive GF16 \
         comparisons={exhaustive}; GF64 shaped comparisons={paired}"
    );
}

#[test]
fn v2_backend_parity() {
    let mut supported = 0;
    for backend in [
        BackendRequest::Auto,
        BackendRequest::Force(BackendId::Portable),
        BackendRequest::Force(BackendId::Pclmul),
        BackendRequest::Force(BackendId::Vpclmul256),
        BackendRequest::Force(BackendId::Vpclmul512),
    ] {
        if Decoder::<Gf64>::new(backend, 1).is_err() {
            continue;
        }
        supported += 1;
        for (words, beta, stages, work) in [(&[1][..], 1, ONE, 13), (&[3, 9][..], 2, TWO, 212)] {
            let fixture = Fixture::new(&[words], false);
            for seed in [0, 1, u64::MAX, 0xd6e8_feb8_6659_fd93] {
                let actual = fixture.run_backend(
                    DecodePlan::v2(),
                    beta,
                    &[],
                    seed,
                    crate::decode::direct::Fault::None,
                    backend,
                );
                assert_eq!(actual, fixture.run(DecodePlan::v2(), beta, &[], seed));
                assert_eq!(actual.stages, stages);
                assert_eq!(actual.work, work);
            }
        }
        for cap in [12, 13, 190, 191, 208, 212] {
            let fixture = Fixture::new(&[&[3, 9]], false);
            let plan = DecodePlan::v2();
            let (_, layout) = fixture.layout(plan, 2, 0);
            let limits = DecodeLimits {
                max_output_per_bucket: 2,
                max_candidate_inputs: 0,
                max_work: WorkUnits(cap),
                max_scratch_bytes: layout.total_bytes(),
            };
            let request = DecodeRequest {
                local: &fixture.local,
                remote: fixture.view(),
                candidates: &[],
                plan: &plan,
                limits: &limits,
            };
            let run = |backend| {
                let decoder = Decoder::new(backend, 0xd6e8_feb8_6659_fd93).unwrap();
                let mut scratch = DecodeScratch::new(&layout).unwrap();
                let mut job = DecodeJob::new(request, &decoder, &mut scratch).unwrap();
                let mut stages = Vec::new();
                while job.next_stage().is_some() {
                    stages.push(job.run_next());
                }
                let used = job.meter.used();
                (stages, used, job.finish().map(|report| report.work))
            };
            assert_eq!(
                run(backend),
                run(BackendRequest::Auto),
                "fixed-seed tight-limit backend identity"
            );
        }
        let fixture = Fixture::new(&[&[0, 6, 18]], false);
        for seed in [0, 1, u64::MAX, 0xd6e8_feb8_6659_fd93] {
            assert_eq!(
                fixture
                    .run_backend(
                        DecodePlan::v2(),
                        3,
                        &[],
                        seed,
                        crate::decode::direct::Fault::None,
                        backend
                    )
                    .rows,
                [Outcome::Decoded(vec![1, 2, 3])],
                "cross-seed complete-bound identity"
            );
        }
    }
    eprintln!("V2 supported backend requests checked={supported}");
}
