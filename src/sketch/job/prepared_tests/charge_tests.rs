//! Public 16x18 native V2 jobs, beta=18, no candidates, matching zero channels,
//! and sixteen genuine pair-difference rows. No preparation/transition bypass.
#![forbid(unsafe_code)]
use {
    super::*,
    crate::backend::test_observer::{self, Entries},
};

const POISON: u64 = 0xface_beef_1234_5678;

fn snapshot(workspace: &mut DecodeWorkspace<'_>, layout: &RowLayout) -> Vec<u64> {
    let (_, difference, row) = workspace.row(layout);
    let mut words = Vec::new();
    for values in [
        difference,
        row.syndromes,
        row.bm,
        row.polynomials,
        row.factors,
        row.square_table,
        row.verification,
        row.roots,
    ] {
        words.extend_from_slice(values);
    }
    for raw in row.raw {
        words.extend([raw.lo, raw.hi]);
    }
    for frame in row.stack {
        words.extend([
            frame.coefficient_start,
            frame.coefficient_len,
            u64::from(frame.next_direction),
            u64::from(frame.split_checked),
        ]);
    }
    words
}

fn backends() -> impl Iterator<Item = BackendId> {
    [
        BackendId::Portable,
        BackendId::Pclmul,
        BackendId::Vpclmul512,
    ]
    .into_iter()
    .filter(|&b| Decoder::<Gf64>::new(BackendRequest::Force(b), 1).is_ok())
}

#[test]
fn failed_first_compare_leaves_kernels_and_row_scratch_untouched() {
    let fixture = Fixture::new(18, &[2; 16], false);
    let plan = DecodePlan::v2();
    let (_, layout) = plan
        .complete_bound(&[18; 16], &[Some(18); 16], 18, 0)
        .unwrap();
    let row_layout = RowLayout::new(18, 18).unwrap();
    for backend in backends() {
        // Admission=17 and Normalize=0 succeed; Compare=19 cannot be charged.
        let limits = DecodeLimits {
            max_output_per_bucket: 18,
            max_candidate_inputs: 0,
            max_work: WorkUnits(17),
            max_scratch_bytes: layout.total_bytes(),
        };
        let decoder = Decoder::new(BackendRequest::Force(backend), 1).unwrap();
        let mut scratch = DecodeScratch::new(&layout).unwrap();
        scratch.words.fill(POISON);
        let before = snapshot(&mut scratch.split(&layout).0, &row_layout);
        test_observer::reset();
        let result = DecodeJob::new(
            DecodeRequest {
                local: &fixture.local,
                remote: fixture.view(),
                candidates: &[],
                plan: &plan,
                limits: &limits,
            },
            &decoder,
            &mut scratch,
        )
        .map(|_| ());
        assert_eq!(result, Err(DecodeError::WorkLimitExceeded));
        let after = snapshot(&mut scratch.split(&layout).0, &row_layout);
        let (mut workspace, _) = scratch.split(&layout);
        let (_, _, row) = workspace.row(&row_layout);
        assert_eq!(
            (
                test_observer::entries(),
                after == before,
                row.factors.iter().all(|&word| word == POISON)
            ),
            (Entries::default(), true, true),
            "failed first Compare must enter no difference/inverse kernel and leave row \
             scratch/factor arena unchanged: {backend:?}"
        );
    }
}

#[test]
fn failed_later_direct_two_keeps_unentered_algebra_and_scratch_untouched() {
    let fixture = Fixture::new(18, &[2; 16], false);
    let plan = DecodePlan::v2();
    let (_, layout) = plan
        .complete_bound(&[18; 16], &[Some(18); 16], 18, 0)
        .unwrap();
    let row_layout = RowLayout::new(18, 18).unwrap();
    let verify = (2 * 18 + 3) * 18 + 18 + 1;
    let canonicalize = 18 * (5 + 1);
    let first_row = 19 + 1 + verify + 168 + verify + canonicalize;
    let prefix = 17 + first_row + 19 + 1 + verify;
    for backend in backends() {
        // Both the exact prefix and one below the later DirectTwo boundary fail.
        for max_work in [prefix, prefix + 167] {
            let limits = DecodeLimits {
                max_output_per_bucket: 18,
                max_candidate_inputs: 0,
                max_work: WorkUnits(max_work),
                max_scratch_bytes: layout.total_bytes(),
            };
            let decoder = Decoder::new(BackendRequest::Force(backend), 1).unwrap();
            let mut scratch = DecodeScratch::new(&layout).unwrap();
            scratch.words.fill(POISON);
            test_observer::reset();
            let mut job = DecodeJob::new(
                DecodeRequest {
                    local: &fixture.local,
                    remote: fixture.view(),
                    candidates: &[],
                    plan: &plan,
                    limits: &limits,
                },
                &decoder,
                &mut scratch,
            )
            .unwrap();
            let constructor_entries = test_observer::entries();
            let mut completed_pairs = 0;
            while !(job.bucket == 1 && job.next_stage() == Some(Stage::DirectTwo)) {
                if job.next_stage() == Some(Stage::DirectTwo) {
                    completed_pairs += 1;
                }
                assert!(matches!(job.run_next(), StageProgress::Completed { .. }));
            }
            assert_eq!(
                completed_pairs, 1,
                "the preceding pair row must actually complete"
            );
            assert_eq!(job.meter.used(), WorkUnits(prefix));
            let before = snapshot(&mut job.workspace, &row_layout);
            let entries_before = test_observer::entries();
            assert_eq!(
                job.run_next(),
                StageProgress::Failed(DecodeError::WorkLimitExceeded)
            );
            let after = snapshot(&mut job.workspace, &row_layout);
            let (_, _, row) = job.workspace.row(&row_layout);
            assert_eq!(
                (
                    constructor_entries,
                    entries_before,
                    test_observer::entries(),
                    after == before,
                    row.factors[2 * 18..].iter().all(|&word| word == POISON)
                ),
                (
                    Entries {
                        differences: 1,
                        inverses: 0
                    },
                    Entries {
                        differences: 2,
                        inverses: 1
                    },
                    Entries {
                        differences: 2,
                        inverses: 1
                    },
                    true,
                    true
                ),
                "failed later DirectTwo must have no speculative inverse or future-row factor \
                 writes and leave its workspace unchanged: {backend:?}"
            );
            assert_eq!(job.meter.used(), WorkUnits(prefix));
            assert_eq!(
                job.run_next(),
                StageProgress::Failed(DecodeError::WorkLimitExceeded)
            );
            assert_eq!(
                job.finish().map(|_| ()),
                Err(DecodeError::WorkLimitExceeded)
            );
        }
    }
}
