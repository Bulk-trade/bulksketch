//! Mode: V3 residual monic-polynomial traversal after charged BM/deflation.
//! Independent polynomial products use only the bit-serial field oracle.
#![forbid(unsafe_code)]

use {
    super::*,
    crate::{
        backend::portable::Portable,
        decode::{bm_tests::multiply, row_tests::Arena},
        field::{Gf64, reference},
        types::WorkUnits,
    },
};

fn polynomial(roots: &[u64]) -> Vec<u64> {
    roots
        .iter()
        .fold(vec![1], |p, &root| multiply::<Gf64>(&p, &[root, 1]))
}

fn mix(seed: &mut u64) -> u64 {
    *seed = seed.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let mut z = *seed;
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

fn solve(modulus: &[u64], seed: u64) -> Result<Vec<u64>, DecodeFailure> {
    let degree = modulus.len() - 1;
    let mut arena = Arena::new(degree, degree, 0xdead);
    let mut w = arena.workspace();
    w.bm[..modulus.len()].copy_from_slice(modulus);
    let mut roots = Roots::default();
    roots.enable_v3();
    roots.set_splitter_seed(seed);
    let mut stage = roots.start(degree, &mut w);
    let mut meter = WorkMeter::new(WorkUnits(u64::MAX));
    while stage != Stage::Verification {
        stage = roots
            .run::<Gf64, Portable>(stage, &mut w, &mut meter)
            .unwrap()?;
    }
    if !affine::preferred::<Gf64>(degree) && degree >= 3 {
        let basis = w
            .basis
            .directions
            .as_ref()
            .expect("trace fallback initialized its seeded basis");
        assert_eq!(
            basis[0],
            seed.max(1),
            "V3 trace fallback preserves caller seed {seed:#x}"
        );
        for (index, &actual) in basis[..w.basis.len as usize].iter().enumerate() {
            assert_eq!(
                actual,
                reference::mul::<Gf64>(seed.max(1), 1_u64 << index),
                "V3 trace fallback seeded coordinate seed={seed:#x} index={index}"
            );
        }
    }
    let mut answer = w.roots[..roots.count].to_vec();
    answer.sort_unstable();
    Ok(answer)
}

#[test]
fn affine_polynomial_corpus() {
    let mut cases = 0;
    let mut state = 0x786f_6f74_6d69_7831;
    for degree in 3..=18 {
        for family in 0..4 {
            for repetition in 0..3 {
                let mut expected = Vec::new();
                while expected.len() < degree {
                    let value = match family {
                        0 => mix(&mut state),
                        1 => u64::try_from(expected.len() + 1).unwrap(),
                        2 => 0xa000_0000_0000_0000 ^ u64::try_from(expected.len() + 1).unwrap(),
                        _ => mix(&mut state) & 0xffff,
                    };
                    if value != 0 && !expected.contains(&value) {
                        expected.push(value);
                    }
                }
                expected.sort_unstable();
                let f = polynomial(&expected);
                assert_eq!(
                    solve(&f, mix(&mut state)),
                    Ok(expected),
                    "V3 residual roots degree={degree} family={family} repetition={repetition}"
                );
                cases += 1;
            }
        }
    }
    // Selected trace fallback must retain caller-seeded coordinates for low IDs.
    for seed in [0, 1, 0x55, 1 << 63, 0xd6e8_feb8_6659_fd93] {
        let expected = (1..=32).collect::<Vec<_>>();
        assert_eq!(solve(&polynomial(&expected), seed), Ok(expected));
        cases += 1;
    }
    println!("ROOTMIX_INDEPENDENT_POLYNOMIAL_POSITIVES {cases}");
}

#[test]
fn affine_rejects_nonsplit_and_repeated_factors() {
    // For this registered GF64 modulus Tr(Z^61)=1; prove it independently.
    let delta = (0..64)
        .map(|bit| 1_u64 << bit)
        .find(|&value| {
            let mut trace = value;
            let mut next = value;
            for _ in 1..64 {
                next = reference::mul::<Gf64>(next, next);
                trace ^= next;
            }
            trace == 1
        })
        .unwrap();
    let irreducible = [delta, 1, 1];
    let mut cases = 0;
    let mut state = 0x7265_6a65_6374_696f;
    for degree in 3..=18 {
        let repeated = polynomial(&(0..degree).map(|i| 1 + (i / 2) as u64).collect::<Vec<_>>());
        assert_eq!(
            solve(&repeated, mix(&mut state)),
            Err(DecodeFailure::NotSplit),
            "V3 repeated-root factor degree={degree}"
        );
        let split = polynomial(&(1..=degree - 2).map(|i| i as u64).collect::<Vec<_>>());
        let nonsplit = multiply::<Gf64>(&irreducible, &split);
        assert_eq!(
            solve(&nonsplit, mix(&mut state)),
            Err(DecodeFailure::NotSplit),
            "V3 irreducible factor degree={degree}"
        );
        let mut arbitrary = (0..degree - 2).map(|_| mix(&mut state)).collect::<Vec<_>>();
        arbitrary.push(1);
        let nonsplit = multiply::<Gf64>(&irreducible, &arbitrary);
        assert_eq!(
            solve(&nonsplit, mix(&mut state)),
            Err(DecodeFailure::NotSplit),
            "V3 irreducible times arbitrary cofactor degree={degree}"
        );
        cases += 3;
    }
    println!("ROOTMIX_INDEPENDENT_POLYNOMIAL_REJECTIONS {cases}");
}

#[derive(Debug, PartialEq, Eq)]
struct Snapshot {
    words: Vec<u64>,
    raw: Vec<(u64, u64)>,
    frames: Vec<(u64, u64, u32, u32)>,
    basis: Option<[u64; 64]>,
    basis_len: u32,
    roots: String,
}

fn snapshot(roots: &Roots, w: &RowWorkspace<'_>) -> Snapshot {
    Snapshot {
        words: [
            &*w.syndromes,
            &*w.bm,
            &*w.polynomials,
            &*w.factors,
            &*w.square_table,
            &*w.verification,
            &*w.roots,
        ]
        .concat(),
        raw: w.raw.iter().map(|p| (p.lo, p.hi)).collect(),
        frames: w
            .stack
            .iter()
            .map(|f| {
                (
                    f.coefficient_start,
                    f.coefficient_len,
                    f.next_direction,
                    f.split_checked,
                )
            })
            .collect(),
        basis: w.basis.directions,
        basis_len: w.basis.len,
        roots: format!("{roots:?}"),
    }
}

#[test]
fn affine_every_integer_failed_charge_executes_nothing() {
    let mut swept = [false; 3];
    let mut limits = 0;
    let mut state = 0x6368_6172_6765_7331;
    for degree in [5, 12] {
        let expected = (0..degree).map(|_| mix(&mut state)).collect::<Vec<_>>();
        let f = polynomial(&expected);
        let mut arena = Arena::new(degree, degree, 0xbad);
        let mut w = arena.workspace();
        w.bm[..f.len()].copy_from_slice(&f);
        let mut roots = Roots::default();
        roots.enable_v3();
        let mut stage = roots.start(degree, &mut w);
        let mut meter = WorkMeter::new(WorkUnits(u64::MAX));
        while stage != Stage::Verification {
            let target = match stage {
                Stage::AffinePreparation => Some((
                    0,
                    Charge::AffinePreparation {
                        degree: roots.degree,
                    },
                )),
                Stage::AffineEnumeration => Some((
                    1,
                    Charge::AffineEnumeration {
                        degree: roots.degree,
                        rank: roots.affine_rank,
                    },
                )),
                Stage::AffineSplit => Some((
                    2,
                    Charge::AffineSplit {
                        degree: roots.degree,
                        rank: roots.affine_rank,
                    },
                )),
                _ => None,
            };
            if let Some((index, operation)) = target.filter(|&(index, _)| !swept[index]) {
                let cost = WorkScheduleV1::cost(operation).unwrap().0;
                let before = snapshot(&roots, &w);
                for max_work in 0..cost {
                    let mut limited = WorkMeter::new(WorkUnits(max_work));
                    assert_eq!(
                        roots.run::<Gf64, Portable>(stage, &mut w, &mut limited),
                        Err(DecodeError::WorkLimitExceeded),
                        "V3 {stage:?} work={max_work} < charge={cost}"
                    );
                    assert_eq!(
                        snapshot(&roots, &w),
                        before,
                        "V3 {stage:?} failed charge changed workspace or counters at \
                         work={max_work}"
                    );
                    assert_eq!(limited.used(), WorkUnits(0));
                    limits += 1;
                }
                swept[index] = true;
            }
            stage = roots
                .run::<Gf64, Portable>(stage, &mut w, &mut meter)
                .unwrap()
                .unwrap();
        }
    }
    assert_eq!(
        swept, [true; 3],
        "every new affine stage reached in V3 traversal"
    );
    println!("ROOTMIX_FAILED_CHARGE_INTEGER_LIMITS {limits}");
}

#[test]
fn affine_charge_goldens_and_derived_selector() {
    for (degree, rank, prepare, enumerate, split) in [
        (3, 2, 18160, 44, 100),
        (5, 4, 19560, 230, 428),
        (12, 11, 31768, 57357, 5482),
        (18, 17, 57130, 5242899, 18160),
    ] {
        for (operation, expected) in [
            (Charge::AffinePreparation { degree }, prepare),
            (Charge::AffineEnumeration { degree, rank }, enumerate),
            (Charge::AffineSplit { degree, rank }, split),
        ] {
            assert_eq!(
                WorkScheduleV1::cost(operation).unwrap(),
                WorkUnits(expected),
                "{operation:?}"
            );
        }
    }
    assert_eq!(affine::MAX_PREFERRED_DEGREE, 18);
    for degree in 0..=89 {
        assert_eq!(
            affine::preferred::<Gf64>(degree),
            (3..=18).contains(&degree)
        );
    }
    for degree in 3..=18 {
        assert_eq!(
            affine::enumerate_preferred(degree, degree - 1),
            degree <= 8,
            "in-row square-mod changes the full-rank enumeration boundary d={degree}"
        );
        assert!(
            affine::enumerate_preferred(degree, degree.next_power_of_two().ilog2() as usize),
            "structured low-rank sets retain enumeration d={degree}"
        );
    }
    assert_eq!(
        WorkScheduleV1::cost(Charge::AffineEnumeration {
            degree: 3,
            rank: 64
        }),
        Err(DecodeError::WorkLimitExceeded)
    );
}

// These degree/rank pairs select splitting, unlike the low-rank rejection corpus.
// With the low-bit prefix annihilators, 3 is in the first GCD, 131 stays in
// the first quotient, and 195 stays in two quotients before entering a GCD.
fn repeated_split_fixtures() -> Vec<Vec<u64>> {
    let known = vec![3, 3, 2, 1, 7, 11, 19, 35, 67, 131];
    let mut fixtures = vec![known];
    for repeated in [3, 67, 131] {
        let mut roots = vec![
            3, 2, 1, 7, 11, 19, 35, 67, 131, 129, 130, 135, 139, 147, 163, 195,
        ];
        roots.push(repeated);
        fixtures.push(roots);
    }
    fixtures.push(vec![
        3, 2, 1, 7, 11, 19, 35, 67, 131, 195, 193, 194, 199, 195,
    ]);
    fixtures
}

fn repeated_split_rejection<F: BinaryField>() {
    let fixtures = repeated_split_fixtures();
    let mut failures = Vec::new();
    for values in &fixtures {
        let f = values
            .iter()
            .fold(vec![1], |p, &r| multiply::<F>(&p, &[r, 1]));
        let degree = values.len();
        // Confirm the fixture's affine map and selector independently of the
        // rejection in Roots::prepare_affine. This is a path witness, not the test.
        let mut arena = Arena::new(degree, degree, 0xdead);
        let w = arena.workspace();
        <Dense as Polynomial<F, Portable>>::prepare_square_table(&f, w.square_table, w.polynomials);
        let (coefficients, work) = w.bm.split_at_mut(degree + 1);
        let len = affine::multiple::<F, Portable>(
            &f,
            w.square_table,
            w.factors,
            coefficients,
            work,
            w.raw,
        );
        let mut basis = [0; 64];
        let (base, rank) =
            affine::solve_map::<F, Portable>(&coefficients[..len], &mut basis).unwrap();
        assert_eq!((base, rank), (0, 8));
        assert_eq!(&basis[..rank], &[1, 2, 4, 8, 16, 32, 64, 128]);
        assert!(!affine::enumerate_preferred(degree, rank));

        for v3 in [false, true] {
            let mut arena = Arena::new(degree, degree, 0xdead);
            let mut w = arena.workspace();
            w.bm[..f.len()].copy_from_slice(&f);
            let mut roots = Roots::default();
            if v3 {
                roots.enable_v3();
            }
            let mut stage = roots.start(degree, &mut w);
            let mut meter = WorkMeter::new(WorkUnits(u64::MAX));
            let mut visited = Vec::new();
            let result = loop {
                if stage == Stage::Verification {
                    break Ok(w.roots[..roots.count].to_vec());
                }
                visited.push(stage);
                match roots.run::<F, Portable>(stage, &mut w, &mut meter).unwrap() {
                    Ok(next) => stage = next,
                    Err(reason) => break Err(reason),
                }
            };
            let expected_work = (8 * degree * degree
                + 2 * degree
                + 5 * degree * degree * degree
                + 16 * degree * degree
                + 327 * degree
                + 16900) as u64;
            if result != Err(DecodeFailure::NotSplit)
                || (v3
                    && (visited != [Stage::ReducerPreparation, Stage::AffinePreparation]
                        || meter.used().0 != expected_work
                        || (roots.count, roots.attempts, roots.gcd_degree) != (0, 0, 0)))
            {
                failures.push(format!(
                    "bits={} v3={v3} roots={values:?} result={result:?} stages={visited:?} \
                     work={} expected_v3_work={expected_work}",
                    F::BITS,
                    meter.used().0
                ));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "repeated split locators must reject as NotSplit at the charged stage:\n{}",
        failures.join("\n")
    );
    println!(
        "ROOTMIX_REPEATED_SPLIT bits={} fixtures={} v2_and_v3=true",
        F::BITS,
        fixtures.len()
    );
}

#[test]
fn repeated_split_gf64() {
    repeated_split_rejection::<Gf64>();
}

#[test]
fn repeated_split_gf256() {
    repeated_split_rejection::<crate::field::tiny::Gf256>();
}

#[test]
fn affine_gf256_polynomial_corpus() {
    use crate::field::tiny::Gf256;
    fn solve(modulus: &[u64]) -> Result<Vec<u64>, DecodeFailure> {
        let degree = modulus.len() - 1;
        let mut arena = Arena::new(degree, degree, 0xdead);
        let mut w = arena.workspace();
        w.bm[..modulus.len()].copy_from_slice(modulus);
        let mut roots = Roots::default();
        roots.enable_v3();
        let mut stage = roots.start(degree, &mut w);
        let mut meter = WorkMeter::new(WorkUnits(u64::MAX));
        while stage != Stage::Verification {
            stage = roots
                .run::<Gf256, Portable>(stage, &mut w, &mut meter)
                .unwrap()?;
        }
        let mut actual = w.roots[..roots.count].to_vec();
        actual.sort_unstable();
        Ok(actual)
    }
    let product = |values: &[u64]| {
        values
            .iter()
            .fold(vec![1], |p, &r| multiply::<Gf256>(&p, &[r, 1]))
    };
    // Independent absolute trace identifies an irreducible X^2+X+delta.
    let delta = (1..=255)
        .find(|&x| {
            let mut trace = x;
            let mut power = x;
            for _ in 1..8 {
                power = reference::mul::<Gf256>(power, power);
                trace ^= power;
            }
            trace == 1
        })
        .unwrap();
    let mut cases = 0;
    let mut state = 0x6766_3235_365f_7633;
    for degree in 3..=18 {
        for family in 0..4 {
            let mut expected = Vec::new();
            while expected.len() < degree {
                let root = match family {
                    0 => expected.len() as u64 + 1,
                    1 => (expected.len() as u64 + 1) ^ 128,
                    _ => mix(&mut state) & 255,
                };
                if root != 0 && !expected.contains(&root) {
                    expected.push(root);
                }
            }
            expected.sort_unstable();
            assert_eq!(solve(&product(&expected)), Ok(expected));
            cases += 1;
        }
        let repeated = (0..degree).map(|i| 1 + (i / 2) as u64).collect::<Vec<_>>();
        assert_eq!(solve(&product(&repeated)), Err(DecodeFailure::NotSplit));
        let split = product(&(1..=degree as u64 - 2).collect::<Vec<_>>());
        assert_eq!(
            solve(&multiply::<Gf256>(&[delta, 1, 1], &split)),
            Err(DecodeFailure::NotSplit)
        );
        let mut arbitrary = (0..degree - 2)
            .map(|_| mix(&mut state) & 255)
            .collect::<Vec<_>>();
        arbitrary.push(1);
        assert_eq!(
            solve(&multiply::<Gf256>(&[delta, 1, 1], &arbitrary)),
            Err(DecodeFailure::NotSplit)
        );
        cases += 3;
    }
    println!("ROOTMIX_GF256_POLYNOMIAL_CASES {cases}");
}
