#![forbid(unsafe_code)]

mod fixture;

use {crate::BackendId, fixture::Outcome};

#[test]
fn v1_work_and_roots_match_base() {
    for line in include_str!("../../../tests/vectors/backend-work-v1.tsv").lines() {
        let values: Vec<u64> = line
            .split_whitespace()
            .map(|s| s.parse().unwrap())
            .collect();
        let buckets = usize::try_from(values[0]).unwrap();
        let capacity = usize::try_from(values[1]).unwrap();
        let degree = usize::try_from(values[2]).unwrap();
        let shift = u32::try_from(values[3]).unwrap();
        let rows = fixture::rows(buckets, degree, shift);
        let (local, remote) = fixture::fixture(buckets, capacity, &rows, BackendId::Portable);
        let (outcomes, work) = fixture::decode(
            &local,
            remote.encoded_v1().unwrap(),
            capacity,
            values[4],
            BackendId::Portable,
            &[],
        )
        .unwrap();
        for (outcome, expected) in outcomes.iter().zip(&rows) {
            assert_eq!(
                *outcome,
                Outcome::Decoded(expected.clone()),
                "base roots: {line}"
            );
        }
        assert_eq!(work.0, values[5], "base logical work: {line}");
    }
}

#[test]
fn forced_backends_match_complete_requests() {
    use crate::{BackendRequest, DecodeError, Decoder, Gf64, WorkUnits};
    if Decoder::<Gf64>::new(BackendRequest::Force(BackendId::Pclmul), 1).is_err() {
        return;
    }
    let mut cases = 0;
    for (buckets, capacity) in [(16, 18), (16, 32), (4, 72), (1, 89)] {
        for degree in [0, 1, 2, capacity / 2, capacity, capacity + 1] {
            for shift in [0, 24, 40] {
                let rows = fixture::rows(buckets, degree, shift);
                let (portable, remote) =
                    fixture::fixture(buckets, capacity, &rows, BackendId::Portable);
                let (hardware, remote_hardware) =
                    fixture::fixture(buckets, capacity, &rows, BackendId::Pclmul);
                assert_eq!(
                    hardware.encoded_v1().unwrap(),
                    portable.encoded_v1().unwrap(),
                    "inserted local bytes"
                );
                assert_eq!(
                    remote_hardware.encoded_v1().unwrap(),
                    remote.encoded_v1().unwrap(),
                    "inserted remote bytes"
                );
                let hints: Vec<_> = rows
                    .iter()
                    .flatten()
                    .copied()
                    .step_by(2)
                    .chain([0, 0])
                    .collect();
                for seed in [0, 1, 0xd6e8_feb8_6659_fd93] {
                    for candidates in [&[][..], hints.as_slice()] {
                        let expected = fixture::decode(
                            &portable,
                            remote.encoded_v1().unwrap(),
                            capacity,
                            seed,
                            BackendId::Portable,
                            candidates,
                        )
                        .unwrap();
                        let actual = fixture::decode(
                            &hardware,
                            remote_hardware.encoded_v1().unwrap(),
                            capacity,
                            seed,
                            BackendId::Pclmul,
                            candidates,
                        )
                        .unwrap();
                        assert_eq!(
                            actual, expected,
                            "complete request: {buckets}x{capacity} d={degree}, shift={shift}, \
                             seed={seed}"
                        );
                        if degree <= capacity {
                            for (outcome, roots) in actual.0.iter().zip(&rows) {
                                let expected = if roots.is_empty() {
                                    Outcome::Equal
                                } else {
                                    Outcome::Decoded(roots.clone())
                                };
                                assert_eq!(*outcome, expected, "within-capacity roots");
                            }
                        }
                        let limit = WorkUnits(expected.1.0 / 2);
                        let left = fixture::decode_with_work(
                            &portable,
                            remote.encoded_v1().unwrap(),
                            capacity,
                            seed,
                            BackendId::Portable,
                            candidates,
                            Some(limit),
                        );
                        let right = fixture::decode_with_work(
                            &hardware,
                            remote_hardware.encoded_v1().unwrap(),
                            capacity,
                            seed,
                            BackendId::Pclmul,
                            candidates,
                            Some(limit),
                        );
                        assert_eq!(left, right, "tight-work backend equality");
                        assert!(
                            matches!(left, Err(DecodeError::WorkLimitExceeded)),
                            "half the actual work cannot finish"
                        );
                        cases += 1;
                    }
                }
            }
        }
    }
    println!("forced-backend complete-request comparisons: {cases}");
}

#[test]
fn difference_includes_the_last_word() {
    let (local, remote) = fixture::fixture(16, 18, &[], BackendId::Portable);
    let mut wire = remote.encoded_v1().unwrap().to_vec();
    *wire.last_mut().unwrap() ^= 1;
    let (outcomes, _) = fixture::decode(&local, &wire, 18, 1, BackendId::Portable, &[]).unwrap();
    assert!(outcomes[..15].iter().all(|row| *row == Outcome::Equal));
    assert!(
        matches!(outcomes[15], Outcome::Failed(_)),
        "a nonzero final syndrome cannot be classified as equal: {:?}",
        outcomes[15]
    );
}
