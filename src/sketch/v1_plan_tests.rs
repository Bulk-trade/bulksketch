#![forbid(unsafe_code)]

use crate::{DecodeError, DecodePlan, DecodeScratch, Gf64, ScratchLayout, WorkUnits};

#[test]
fn plan_bounds_and_layout() {
    let plan = DecodePlan::v1();
    let (work, layout) = plan
        .complete_bound(&[1, 1], &[None, Some(0)], 0, 1)
        .unwrap();
    assert_eq!(
        work,
        WorkUnits(285),
        "V1 complete bound includes request preprocessing once and only the admitted row"
    );
    assert_eq!(
        layout.total_bytes(),
        192,
        "18 words + two fixed-width 24-byte outcomes; zero-failed row has no workspace/results"
    );
    assert_eq!(
        layout,
        ScratchLayout::for_plan(&plan, &[1, 1], &[None, Some(0)], 0, 1).unwrap()
    );
    DecodeScratch::<Gf64>::new(&layout).unwrap();
    let (work, layout) = plan.complete_bound(&[1], &[Some(1)], 1, 0).unwrap();
    assert_eq!(work, WorkUnits(459));
    assert_eq!(
        layout.total_bytes(),
        472,
        "all typed segments, result ID and metadata are included"
    );
    let (_, layout) = plan.complete_bound(&[1], &[None], 0, 1).unwrap();
    assert_eq!(
        layout.total_bytes(),
        56,
        "a zero-only preclassified row still requires metadata, candidates and routing offsets"
    );
    assert_eq!(
        plan.complete_bound(&[1], &[Some(0)], 0, usize::MAX)
            .unwrap_err(),
        DecodeError::WorkLimitExceeded
    );
    assert_eq!(
        ScratchLayout::for_plan(&plan, &[1], &[Some(0)], 0, usize::MAX).unwrap_err(),
        DecodeError::ScratchTooSmall
    );
    for (capacities, budgets, beta) in [
        (&[][..], &[][..], 0),
        (&[1][..], &[][..], 0),
        (&[0][..], &[Some(0)][..], 0),
        (&[1][..], &[Some(2)][..], 2),
        (&[1][..], &[Some(1)][..], 0),
        (&[2][..], &[Some(0)][..], 2),
        (&[1][..], &[None][..], 1),
    ] {
        assert_eq!(
            plan.complete_bound(capacities, budgets, beta, 0)
                .unwrap_err(),
            DecodeError::InvalidPlan
        );
    }
}
