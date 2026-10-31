//! Public native V2, warm immutable 16x18 encoding, equal independently allocated
//! remote bytes, beta=18 and no candidates. No shortcut or stage bypass.
#![forbid(unsafe_code)]
use {super::*, crate::backend::test_observer};

fn failed_compare(charged_rows: usize) {
    let fixture = Fixture::new(18, &[0; 16], false);
    let cached = fixture.local.encoded_v1().unwrap();
    assert_eq!(cached, fixture.remote.as_slice());
    assert_ne!(cached.as_ptr(), fixture.remote.as_ptr());
    let plan = DecodePlan::v2();
    let (_, layout) = plan
        .complete_bound(&[18; 16], &[Some(18); 16], 18, 0)
        .unwrap();
    for backend in [
        BackendId::Portable,
        BackendId::Pclmul,
        BackendId::Vpclmul512,
    ] {
        let Ok(decoder) = Decoder::new(BackendRequest::Force(backend), 1) else {
            continue;
        };
        for slack in [0, 18] {
            let limits = DecodeLimits {
                max_output_per_bucket: 18,
                max_candidate_inputs: 0,
                // Admission=17, Normalize=0, each successful Compare=19.
                max_work: WorkUnits(17 + 19 * charged_rows as u64 + slack),
                max_scratch_bytes: layout.total_bytes(),
            };
            let mut scratch = DecodeScratch::new(&layout).unwrap();
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
            let cached = test_observer::cached_comparisons();
            let kernels = test_observer::entries();
            assert!(
                cached.end <= charged_rows
                    && cached.rows + kernels.differences == charged_rows
                    && kernels.inverses == 0,
                "failed Compare must inspect no cached bytes of an uncharged row: \
                 charged_rows={charged_rows} backend={backend:?} slack={slack} cached={cached:?} \
                 kernels={kernels:?}"
            );
        }
    }
}

#[test]
fn warm_equal_failed_first_compare_inspects_no_cached_bytes() {
    failed_compare(0);
}

#[test]
fn warm_equal_failed_later_compare_inspects_only_charged_rows() {
    for charged_rows in [1, 7, 15] {
        failed_compare(charged_rows);
    }
}
