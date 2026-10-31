//! One admitted multirow V2 request, exact stage/work parity with unprepared execution.
#![forbid(unsafe_code)]
use {
    super::*,
    crate::{
        BackendId, BackendRequest, DecodeLimits, DecodePlan, FrozenSketch, Gf64, MutableSketch,
        ParseLimits, ShapeLimits, SketchShape, SketchView, WorkUnits, field::reference,
    },
    std::sync::Arc,
};

struct Fixture {
    local: FrozenSketch<Gf64>,
    remote: Vec<u8>,
    zero: bool,
}
impl Fixture {
    fn new(c: usize, degrees: &[usize], zero: bool) -> Self {
        let caps = vec![c; degrees.len()];
        let shape = Arc::new(
            SketchShape::new(
                &caps,
                &ShapeLimits {
                    max_wire_bytes: 100_000,
                    max_buckets: 64,
                    max_capacity_per_bucket: 100,
                    max_total_syndrome_words: 6400,
                },
            )
            .unwrap(),
        );
        let local = MutableSketch::new(shape, BackendRequest::Force(BackendId::Portable))
            .unwrap()
            .freeze();
        let mut remote = local.encoded_v1().unwrap().to_vec();
        let start = 24 + 2 * degrees.len();
        remote[start] = u8::from(zero);
        let start = start + degrees.len().div_ceil(8);
        for (b, &d) in degrees.iter().enumerate() {
            let mut odd = vec![0; c];
            for j in 0..d {
                let root = ((j + 1) * degrees.len() + b) as u64;
                let step = reference::mul::<Gf64>(root, root);
                let mut power = root;
                for word in &mut odd {
                    *word ^= power;
                    power = reference::mul::<Gf64>(power, step);
                }
            }
            for (j, word) in odd.iter().enumerate() {
                remote[start + 8 * (b * c + j)..start + 8 * (b * c + j + 1)]
                    .copy_from_slice(&word.to_le_bytes());
            }
        }
        Self {
            local,
            remote,
            zero,
        }
    }
    fn view(&self) -> SketchView<'_, Gf64> {
        SketchView::parse(
            &self.remote,
            &ParseLimits {
                max_wire_bytes: 100_000,
                max_buckets: 64,
                max_capacity_per_bucket: 100,
                max_total_syndrome_words: 6400,
            },
        )
        .unwrap()
    }
    fn run(
        &self,
        beta: usize,
        hints: &[u64],
        backend: BackendId,
        skip: bool,
        max_work: u64,
    ) -> (String, Vec<String>, Vec<u64>) {
        let plan = DecodePlan::v2();
        let budgets: Vec<_> = (0..self.local.shape().bucket_count())
            .map(|b| beta.checked_sub(usize::from(b == 0 && self.zero)))
            .collect();
        let (_, layout) = plan
            .complete_bound(self.local.shape().capacities(), &budgets, beta, hints.len())
            .unwrap();
        let limits = DecodeLimits {
            max_output_per_bucket: beta,
            max_candidate_inputs: hints.len(),
            max_work: WorkUnits(max_work),
            max_scratch_bytes: layout.total_bytes(),
        };
        let mut arena = DecodeScratch::new(&layout).unwrap();
        let mut decoder =
            Decoder::new(BackendRequest::Force(backend), 0xd6e8_feb8_6659_fd93).unwrap();
        decoder.skip_shortcuts = skip;
        let mut stages = Vec::new();
        let mut boundaries = Vec::new();
        crate::backend::test_observer::reset();
        let result = DecodeJob::new(
            DecodeRequest {
                local: &self.local,
                remote: self.view(),
                candidates: hints,
                plan: &plan,
                limits: &limits,
            },
            &decoder,
            &mut arena,
        );
        let Ok(mut job) = result else {
            return (format!("{:?}", result.unwrap_err()), stages, boundaries);
        };
        if skip {
            assert!(
                crate::backend::test_observer::cached_comparisons().rows == 0,
                "reference execution bypasses cached comparisons"
            );
        }
        while job.next_stage().is_some() {
            let progress = job.run_next();
            if let StageProgress::Completed { work, .. } = progress {
                boundaries.push(work.0);
            }
            stages.push(format!("{progress:?}"));
        }
        if let JobState::Error(error) = job.state {
            assert_eq!(job.run_next(), StageProgress::Failed(error));
            assert_eq!(job.run_next(), StageProgress::Failed(error));
        }
        let result = match job.finish() {
            Err(e) => format!("{e:?}"),
            Ok(report) => format!(
                "{:?};work={:?};peak={}",
                (0..self.local.shape().bucket_count())
                    .map(|b| format!("{:?}", report.outcome(b).unwrap()))
                    .collect::<Vec<_>>(),
                report.work,
                report.peak_scratch_bytes
            ),
        };
        (result, stages, boundaries)
    }
}
#[test]
fn prepared_request_preserves_v2_stages_and_cutoffs() {
    let mut backends = vec![BackendId::Portable];
    for b in [BackendId::Pclmul, BackendId::Vpclmul512] {
        if Decoder::<Gf64>::new(BackendRequest::Force(b), 1).is_ok() {
            backends.push(b);
        }
    }
    let mut requests = 0;
    for c in [18, 32, 72, 89] {
        for pattern in 0..7 {
            let mut degrees = vec![0; 16];
            match pattern {
                1 => degrees[2] = 1,
                2 => degrees[2] = 2,
                3 => {
                    for b in [0, 7, 15] {
                        degrees[b] = 2;
                    }
                }
                4 => degrees.fill(2),
                5 => {
                    degrees.fill(2);
                    degrees[0] = 3;
                }
                6 => {
                    degrees[0] = 1;
                    degrees[15] = 2;
                }
                _ => {}
            }
            let mut f = Fixture::new(c, &degrees, pattern == 6);
            if pattern == 6 {
                let last = f.remote.len() - 1;
                f.remote[last] ^= 0x80;
            }
            for beta in [0, 1, 2, c] {
                for hints in [&[][..], &[0, 17, 17, 32][..]] {
                    let reference = f.run(beta, hints, BackendId::Portable, true, u64::MAX);
                    for &backend in &backends {
                        let actual = f.run(beta, hints, backend, false, u64::MAX);
                        assert_eq!(
                            actual, reference,
                            "c={c} pattern={pattern} beta={beta} backend={backend:?}"
                        );
                        requests += 1;
                        if c == 18 && hints.is_empty() && beta == c {
                            let mut cutoffs = vec![0, 1, 2, 3, 15, 16, 17, 24, 25];
                            for &w in &reference.2 {
                                cutoffs.extend([w.saturating_sub(1), w, w + 1]);
                            }
                            cutoffs.sort_unstable();
                            cutoffs.dedup();
                            for limit in cutoffs {
                                assert_eq!(
                                    f.run(beta, hints, backend, false, limit),
                                    f.run(beta, hints, BackendId::Portable, true, limit),
                                    "cutoff {limit} pattern={pattern}"
                                );
                                requests += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    println!("P4_REQUEST_PARITY comparisons={requests} stages_work_outcomes_sticky=true");
}

#[test]
fn prepared_fallback_preserves_budget64() {
    for degree in [16, 32, 64, 65] {
        let f = Fixture::new(89, &[degree; 16], false);
        let expected = f.run(64, &[], BackendId::Portable, true, u64::MAX);
        assert_eq!(
            expected.0.matches("Decoded").count(),
            if degree <= 64 { 16 } else { 0 },
            "independent within-budget success expectation"
        );
        for b in [
            BackendId::Portable,
            BackendId::Pclmul,
            BackendId::Vpclmul512,
        ] {
            if Decoder::<Gf64>::new(BackendRequest::Force(b), 1).is_ok() {
                assert_eq!(
                    f.run(64, &[], b, false, u64::MAX),
                    expected,
                    "c89 beta64 degree{degree} backend{b:?}"
                );
            }
        }
    }
}

#[test]
fn whole_equality_keeps_zero_admission_and_cold_cache() {
    for zero in [false, true] {
        for cold in [false, true] {
            let mut f = Fixture::new(18, &[0; 16], zero);
            if cold {
                let mut mutable = f
                    .local
                    .thaw(BackendRequest::Force(BackendId::Portable))
                    .unwrap();
                mutable.toggle(17);
                mutable.toggle(17);
                f.local = mutable.freeze();
            }
            let plan = DecodePlan::v2();
            let beta: usize = 1;
            let budgets: Vec<_> = (0..16)
                .map(|b| beta.checked_sub(usize::from(b == 0 && zero)))
                .collect();
            let (bound, layout) = plan
                .complete_bound(f.local.shape().capacities(), &budgets, beta, 0)
                .unwrap();
            let limits = DecodeLimits {
                max_output_per_bucket: beta,
                max_candidate_inputs: 0,
                max_work: bound,
                max_scratch_bytes: layout.total_bytes(),
            };
            let decoder = Decoder::new(BackendRequest::Auto, 1).unwrap();
            let mut arena = DecodeScratch::new(&layout).unwrap();
            crate::backend::test_observer::reset();
            let job = DecodeJob::new(
                DecodeRequest {
                    local: &f.local,
                    remote: f.view(),
                    candidates: &[],
                    plan: &plan,
                    limits: &limits,
                },
                &decoder,
                &mut arena,
            )
            .unwrap();
            assert_eq!(
                crate::backend::test_observer::cached_comparisons().rows,
                if !zero && !cold { 16 } else { 0 },
                "cached row equality requires matching zero and warm bytes"
            );
            let report = job.finish().unwrap();
            assert_eq!(
                report.outcome(0),
                Some(if zero {
                    DecodeOutcome::Decoded { ids: &[0] }
                } else {
                    DecodeOutcome::Equal
                })
            );
            assert_eq!(
                f.local.state.encoded_v1.get().is_none(),
                cold,
                "no cache population"
            );
            for work in [0, 1, 16, 17, 32, 33, 64, 320, 321, 322, 1000, u64::MAX] {
                assert_eq!(
                    f.run(beta, &[], BackendId::Portable, false, work),
                    f.run(beta, &[], BackendId::Portable, true, work),
                    "equal charge cutoff {work}"
                );
            }
        }
    }
}

mod cached_compare_tests;
mod charge_tests;
