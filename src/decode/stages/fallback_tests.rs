//! Production mode: V3 no-hint c89/d5 after real tiny-probe fallback, BM,
//! candidate/deflation and affine root recovery, immediately before verification.
#![forbid(unsafe_code)]

use {
    super::*,
    crate::{
        backend::portable::Portable,
        decode::row_tests::{Arena, Outcome, own},
        field::{Gf64, reference},
        types::WorkUnits,
    },
    std::sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    },
};

fn workspace_words(workspace: &RowWorkspace<'_>) -> Vec<u64> {
    let mut words = Vec::new();
    for segment in [
        &*workspace.syndromes,
        &*workspace.bm,
        &*workspace.polynomials,
        &*workspace.factors,
        &*workspace.square_table,
        &*workspace.verification,
        &*workspace.roots,
    ] {
        words.extend_from_slice(segment);
    }
    for raw in &*workspace.raw {
        words.extend_from_slice(&[raw.lo, raw.hi]);
    }
    for frame in &*workspace.stack {
        words.extend_from_slice(&[
            frame.coefficient_start,
            frame.coefficient_len,
            u64::from(frame.next_direction),
            u64::from(frame.split_checked),
        ]);
    }
    words.push(u64::from(workspace.basis.len));
    words.push(u64::from(workspace.basis.directions.is_some()));
    if let Some(directions) = &workspace.basis.directions {
        words.extend_from_slice(directions);
    }
    words
}

fn failed_charge<K: BulkKernels<Gf64> + std::fmt::Debug>() -> usize {
    let capacity = 89;
    let degree = 5;
    let ids = [0x13, 0x223, 0x3333, 0x44443, 0x555553];
    let mut odd = vec![0; capacity];
    for &id in &ids {
        let square = reference::mul::<Gf64>(id, id);
        let mut power = id;
        for (index, word) in odd.iter_mut().enumerate() {
            *word ^= power;
            if index + 1 < capacity {
                power = reference::mul::<Gf64>(power, square);
            }
        }
    }
    let input = RowInput {
        difference: &odd,
        candidates: &[],
    };
    let mut arena = Arena::new(capacity, capacity, 0xdead_beef_cafe_babe);
    let mut workspace = arena.workspace();
    let mut row = <BinaryDecoder as RowDecoder<Gf64, K>>::begin(RowBudget {
        nonzero: capacity,
        total: capacity,
    });
    row.enable_v3();
    row.set_splitter_seed(0xa11f_1e57_1234_5678);
    row.start_probes(&odd);
    let observer = Arc::new(AtomicUsize::new(0));
    row.operation_observer = Some(Arc::clone(&observer));
    let mut initial_meter = WorkMeter::new(WorkUnits(u64::MAX));
    let mut stages = Vec::new();
    while row.next_stage() != Some(Stage::Verification) || row.probe.is_some() {
        assert!(
            row.next_stage().is_some(),
            "fixture must reach general LFSR verification"
        );
        stages.push(
            row.run_next(input, &mut workspace, &mut initial_meter)
                .unwrap()
                .stage,
        );
    }
    assert!(stages.contains(&Stage::BerlekampMassey));
    assert!(stages.contains(&Stage::AffinePreparation));
    assert_eq!(row.degree, degree);
    assert_eq!(row.roots.count, degree);
    assert!(row.probe.is_none());
    assert!(verify::use_rebuilt_lfsr(degree, capacity));
    let charge = WorkScheduleV1::cost(Charge::VerifyLfsr {
        capacity,
        output_budget: capacity,
        degree,
    })
    .unwrap();
    assert_eq!(
        charge,
        WorkUnits(((3 * degree + 4) * capacity + degree + capacity + 3) as u64)
    );
    let before_workspace = workspace_words(&workspace);
    let before_row = format!("{row:?}");
    let before_observer = observer.load(Ordering::Relaxed);
    for limit in 0..charge.0 {
        let mut meter = WorkMeter::new(WorkUnits(limit));
        assert_eq!(
            row.verify(input, &mut workspace, &mut meter),
            Err(DecodeError::WorkLimitExceeded),
            "LFSR charge must fail at limit {limit}"
        );
        assert_eq!(
            workspace_words(&workspace),
            before_workspace,
            "failed LFSR charge changed workspace at limit {limit}"
        );
        assert_eq!(
            format!("{row:?}"),
            before_row,
            "failed LFSR charge changed state or counters at limit {limit}"
        );
        assert_eq!(
            observer.load(Ordering::Relaxed),
            before_observer,
            "failed LFSR charge executed at limit {limit}"
        );
        assert_eq!(meter.used(), WorkUnits(0));
        assert_eq!(
            meter.charge(WorkUnits(0)),
            Err(DecodeError::WorkLimitExceeded)
        );
    }
    let mut exact = WorkMeter::new(charge);
    let progress = row.run_next(input, &mut workspace, &mut exact).unwrap();
    assert_eq!(progress.stage, Stage::Verification);
    assert_eq!(row.next_stage(), Some(Stage::Canonicalization));
    assert_eq!(exact.used(), charge);
    assert_eq!(observer.load(Ordering::Relaxed), before_observer + 1);
    let result = row
        .finish(
            input,
            &mut workspace,
            &mut WorkMeter::new(WorkUnits(u64::MAX)),
        )
        .unwrap();
    assert_eq!(own(&result), Outcome::Decoded(ids.to_vec()));
    charge.0 as usize
}

#[test]
fn lfsr_every_integer_failed_charge_is_inert() {
    let failed_limits = failed_charge::<Portable>();
    #[cfg(target_arch = "x86_64")]
    let failed_limits = {
        let mut failed_limits = failed_limits;
        use crate::{
            backend::detect,
            types::{BackendId, BackendRequest},
        };
        if detect::resolve(BackendRequest::Force(BackendId::Pclmul)).is_ok() {
            failed_limits += failed_charge::<crate::backend::x86_pclmul::Pclmul>();
        }
        if detect::resolve(BackendRequest::Force(BackendId::Vpclmul512)).is_ok() {
            failed_limits += failed_charge::<crate::backend::x86_vpclmul512::Vpclmul512>();
        }
        failed_limits
    };
    eprintln!("ROOTMIX_LFSR_CHARGE failed_limits={failed_limits} exact_boundary_passed=true");
}

// Mode: an arbitrary residual monic locator at the real row/root-finder
// boundary. This does not assert that public binary BM produces this locator.
fn repeated_affine_progress<F: BinaryField>() {
    let values = [3, 3, 2, 1, 7, 11, 19, 35, 67, 131];
    let degree = values.len();
    let polynomial = values.iter().fold(vec![1], |p, &root| {
        crate::decode::bm_tests::multiply::<F>(&p, &[root, 1])
    });
    let difference = vec![1; degree];
    let input = RowInput {
        difference: &difference,
        candidates: &[],
    };
    let prepare = (5 * degree.pow(3) + 16 * degree.pow(2) + 327 * degree + 16900) as u64;
    let table = (8 * degree.pow(2) + 2 * degree) as u64;
    for limit in [table, table + prepare - 1, table + prepare, u64::MAX] {
        let mut arena = Arena::new(degree, degree, 0xdead);
        let mut w = arena.workspace();
        w.bm[..polynomial.len()].copy_from_slice(&polynomial);
        let mut row = <BinaryDecoder as RowDecoder<F, Portable>>::begin(RowBudget {
            nonzero: degree,
            total: degree,
        });
        row.enable_v3();
        row.degree = degree;
        row.state = State::Running(row.roots.start(degree, &mut w));
        let mut meter = WorkMeter::new(WorkUnits(limit));
        assert_eq!(
            row.run_next(input, &mut w, &mut meter).unwrap().stage,
            Stage::ReducerPreparation
        );
        assert_eq!(meter.used(), WorkUnits(table));
        assert_eq!(row.next_stage(), Some(Stage::AffinePreparation));
        let before = workspace_words(&w);
        let result = row.run_next(input, &mut w, &mut meter);
        assert_eq!(
            row.next_stage(),
            None,
            "repeated locator terminates at charged preparation"
        );
        if limit < table + prepare {
            assert!(matches!(result, Err(DecodeError::WorkLimitExceeded)));
            assert_eq!(workspace_words(&w), before);
            assert_eq!(meter.used(), WorkUnits(table));
            assert!(matches!(
                row.completed_result(&w),
                Err(DecodeError::WorkLimitExceeded)
            ));
            assert_eq!(
                meter.charge(WorkUnits(0)),
                Err(DecodeError::WorkLimitExceeded)
            );
        } else {
            let progress = result.unwrap();
            assert_eq!(progress.stage, Stage::AffinePreparation);
            assert_eq!(progress.locator_degree, degree);
            assert_eq!(
                (
                    progress.candidate_hits,
                    progress.trace_attempts,
                    progress.gcd_degree
                ),
                (0, 0, 0)
            );
            assert_eq!(meter.used(), WorkUnits(table + prepare));
            assert_eq!(
                own(&row.completed_result(&w).unwrap()),
                Outcome::Failed(DecodeFailure::NotSplit)
            );
        }
        assert_eq!(row.next_stage(), None);
        assert_eq!(row.provisional_count(), 0);
        assert_eq!(w.roots, vec![0xdead; degree]);
        let used = meter.used();
        let result = row.finish(input, &mut w, &mut meter);
        if limit < table + prepare {
            assert!(matches!(result, Err(DecodeError::WorkLimitExceeded)));
        } else {
            assert_eq!(
                own(&result.unwrap()),
                Outcome::Failed(DecodeFailure::NotSplit)
            );
        }
        assert_eq!(
            meter.used(),
            used,
            "terminal finish adds no root-finder work"
        );
    }
    println!(
        "ROOTMIX_REPEATED_PROGRESS bits={} exact_work={} limits=4",
        F::BITS,
        table + prepare
    );
}

#[test]
fn repeated_progress_gf64() {
    repeated_affine_progress::<Gf64>();
}

#[test]
fn repeated_progress_gf256() {
    repeated_affine_progress::<crate::field::tiny::Gf256>();
}
