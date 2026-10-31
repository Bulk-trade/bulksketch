//! Repeated-square division and brute-force roots share no production polynomial code.
#![forbid(unsafe_code)]
use {
    super::*,
    crate::{
        backend::portable::Portable,
        decode::{
            bm_tests::{divide, multiply},
            row::{RowBudget, RowDecoder, RowExecution, RowInput},
            row_tests::{Arena, Outcome, odd, own},
            stages::BinaryDecoder,
        },
        field::{
            Gf64, reference,
            tiny::{Gf4, Gf16},
        },
        types::WorkUnits,
    },
};
fn oracle_trace<F: BinaryField>(f: &[u64], a: u64) -> Vec<u64> {
    let mut t = vec![0, a];
    for _ in 1..F::BITS {
        t = divide::<F>(&multiply::<F>(&t, &t), f).1;
        t.resize(t.len().max(2), 0);
        t[1] ^= a;
        while t.last() == Some(&0) {
            t.pop();
        }
    }
    t
}
fn evaluate<F: BinaryField>(p: &[u64], x: u64) -> u64 {
    let mut power = 1;
    let mut value = 0;
    for &c in p {
        value ^= reference::mul::<F>(c, power);
        power = reference::mul::<F>(power, x);
    }
    value
}
fn solve<F: BinaryField>(modulus: &[u64]) -> (Result<Vec<u64>, DecodeFailure>, usize) {
    let degree = modulus.len() - 1;
    let mut arena = Arena::new(degree.max(1), degree, 0xbad);
    let mut workspace = arena.workspace();
    workspace.bm[..modulus.len()].copy_from_slice(modulus);
    let mut roots = Roots::default();
    let mut stage = roots.start(degree, &mut workspace);
    let mut meter = WorkMeter::new(WorkUnits(u64::MAX));
    while stage != Stage::Verification {
        let expected = if stage == Stage::Trace {
            Some(oracle_trace::<F>(
                &workspace.polynomials[..=roots.degree],
                1 << roots.direction,
            ))
        } else {
            None
        };
        match roots
            .run::<F, Portable>(stage, &mut workspace, &mut meter)
            .unwrap()
        {
            Ok(next) => stage = next,
            Err(failure) => return (Err(failure), roots.attempts),
        }
        if let Some(expected) = expected {
            let offset = roots.degree + 1;
            assert_eq!(
                &workspace.polynomials[offset..offset + roots.trace_len],
                expected,
                "trace equals repeated-square division bits={} modulus={modulus:?}",
                F::BITS
            );
        }
    }
    let mut result = workspace.roots[..roots.count].to_vec();
    result.sort_unstable();
    (Ok(result), roots.attempts)
}
#[test]
fn trace_roots_match_independent_oracles() {
    fn enumerate<F: BinaryField>(max_degree: usize) {
        for d in 1..=max_degree {
            for mut code in 0..(F::MASK + 1).pow(u32::try_from(d).unwrap()) {
                let mut f = vec![0; d + 1];
                for v in &mut f[..d] {
                    *v = code & (F::MASK);
                    code >>= F::BITS;
                }
                f[d] = 1;
                if f[0] == 0 {
                    continue;
                }
                let expected = (1..=F::MASK)
                    .filter(|&x| evaluate::<F>(&f, x) == 0)
                    .collect::<Vec<_>>();
                let (actual, _) = solve::<F>(&f);
                if expected.len() == d {
                    assert_eq!(actual, Ok(expected), "brute roots bits={} f={f:?}", F::BITS);
                } else {
                    assert!(
                        actual.is_err(),
                        "nonsplit or repeated roots bits={} f={f:?} actual={actual:?}",
                        F::BITS
                    );
                }
            }
        }
    }
    enumerate::<Gf4>(4);
    enumerate::<Gf16>(3);
    // X^3+1 reaches a normalized-empty trace over this even-degree field.
    let (answer, _) = solve::<Gf64>(&[1, 0, 0, 1]);
    let answer = answer.expect("X^3+1 is split and squarefree");
    assert_eq!(answer.len(), 3);
    for &root in &answer {
        assert_eq!(evaluate::<Gf64>(&[1, 0, 0, 1], root), 0);
    }
    let roots = (1..=16).collect::<Vec<_>>();
    let mut f = vec![1];
    for &r in &roots {
        f = multiply::<Gf64>(&f, &[r, 1]);
    }
    let (answer, attempts) = solve::<Gf64>(&f);
    assert_eq!(answer, Ok(roots));
    assert!(
        attempts >= 8,
        "structured initial trace coordinates must be exercised: attempts={attempts}"
    );
}
#[test]
fn child_failure_is_transactional() {
    let values = odd::<Gf16>(&[1, 2, 3, 4, 5], 5);
    let input = RowInput {
        difference: &values,
        candidates: &[],
    };
    let mut arena = Arena::new(5, 5, 99);
    let mut w = arena.workspace();
    let mut e = <BinaryDecoder as RowDecoder<Gf16, Portable>>::begin(RowBudget {
        nonzero: 5,
        total: 5,
    });
    let mut meter = WorkMeter::new(WorkUnits(u64::MAX));
    let mut first_leaf = false;
    while e.next_stage().is_some() {
        let stage = e.next_stage().unwrap();
        if first_leaf && stage == Stage::Leaf {
            // Inject a zero-root child after a completed sibling. The actual
            // traversal and consuming finish must discard the parent's transaction.
            w.polynomials[0] = 0;
            break;
        }
        e.run_next(input, &mut w, &mut meter).unwrap();
        if stage == Stage::Leaf {
            first_leaf = true;
        }
    }
    assert!(first_leaf, "a sibling completed before child failure");
    assert_eq!(
        own(&e.finish(input, &mut w, &mut meter).unwrap()),
        Outcome::Failed(DecodeFailure::InvalidLocator),
        "no sibling root escapes a failed parent"
    );
}

#[test]
fn basis_extends_only_through_charged_directions() {
    let mut arena = Arena::new(32, 32, 0xbad);
    for seed in [1, 1 << 63, 0xd6e8_feb8_6659_fd93] {
        let expected_roots: Vec<_> = (1..=32).collect();
        let mut modulus = vec![1];
        for &root in &expected_roots {
            modulus = multiply::<Gf64>(&modulus, &[root, 1]);
        }
        let mut workspace = arena.workspace();
        workspace.bm[..modulus.len()].copy_from_slice(&modulus);
        let mut roots = Roots::default();
        roots.set_splitter_seed(seed);
        let mut stage = roots.start(32, &mut workspace);
        let mut meter = WorkMeter::new(WorkUnits(u64::MAX));
        let mut reached = 0;
        let mut resumed = false;
        while stage != Stage::Verification {
            let direction = roots.direction as usize;
            let expected = (stage == Stage::Trace).then(|| {
                oracle_trace::<Gf64>(
                    &workspace.polynomials[..=roots.degree],
                    reference::mul::<Gf64>(seed, 1 << direction),
                )
            });
            if stage == Stage::Trace && roots.attempts == 0 {
                let mut empty = WorkMeter::new(WorkUnits(0));
                assert_eq!(
                    roots.run::<Gf64, Portable>(stage, &mut workspace, &mut empty),
                    Err(DecodeError::WorkLimitExceeded)
                );
                assert!(
                    workspace.basis.directions.is_none(),
                    "no basis before a successful Trace charge"
                );
            }
            stage = roots
                .run::<Gf64, Portable>(stage, &mut workspace, &mut meter)
                .unwrap()
                .unwrap();
            if let Some(expected) = expected {
                resumed |= direction < reached;
                reached = reached.max(direction);
                let basis = workspace.basis.directions.as_ref().unwrap();
                for (j, &element) in basis.iter().enumerate() {
                    let expected = if j <= reached {
                        reference::mul::<Gf64>(seed, 1 << j)
                    } else {
                        0
                    };
                    assert_eq!(
                        element, expected,
                        "only the reached basis prefix: seed={seed:#x} j={j} reached={reached}"
                    );
                }
                let offset = roots.degree + 1;
                assert_eq!(
                    &workspace.polynomials[offset..offset + roots.trace_len],
                    expected,
                    "Trace uses s*Z^j, including resumed siblings: seed={seed:#x} \
                     direction={direction}"
                );
            }
        }
        assert!(
            resumed,
            "fixture resumes an earlier sibling after deeper directions"
        );
        let mut actual = workspace.roots[..roots.count].to_vec();
        actual.sort_unstable();
        assert_eq!(actual, expected_roots);
    }
}
