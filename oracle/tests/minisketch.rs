//! Differential checks of `bulksketch` against both minisketch implementations
//! (impl 0, portable; impl 1, CLMUL when the CPU has it), over every capacity
//! from 1 to 89.
#![forbid(unsafe_code)]

use bulksketch_oracle::{
    Row, bulk_decode_row, bulk_row, ids, minisketch, minisketch_bytes, minisketch_decode, payload,
    symmetric_difference,
};

const MAX_CAPACITY: usize = 89;
const SHARED: usize = 7;

/// Split `diff` between two sides that also share `SHARED` common IDs.
fn sides(stream: u64, diff: &[u64]) -> (Vec<u64>, Vec<u64>) {
    let shared = ids(stream ^ 0x5eed, SHARED);
    let mut local = shared.clone();
    let mut remote = shared;
    for (i, &id) in diff.iter().enumerate() {
        if i % 2 == 0 {
            local.push(id);
        } else {
            remote.push(id);
        }
    }
    (local, remote)
}

/// Decoded output of minisketch for the merged pair, per available implementation.
fn minisketch_results(capacity: usize, local: &[u64], remote: &[u64]) -> Vec<Option<Vec<u64>>> {
    let mut results = Vec::new();
    for implementation in [0, 1] {
        let Some(mut a) = minisketch(implementation, capacity, local) else {
            assert_eq!(implementation, 1, "impl 0 is always available");
            continue;
        };
        let b = minisketch(implementation, capacity, remote).unwrap();
        a.merge(&b).unwrap();
        results.push(minisketch_decode(&a));
    }
    results
}

#[test]
fn row_payload_bytes_match_minisketch() {
    let mut cases = 0;
    for capacity in 1..=MAX_CAPACITY {
        for count in [
            0,
            1,
            capacity / 2,
            capacity,
            capacity + 1,
            3 * capacity,
            200,
        ] {
            let set = ids(capacity as u64 * 1000 + count as u64, count);
            let ours = bulk_row(capacity, &set);
            for implementation in [0, 1] {
                let Some(theirs) = minisketch(implementation, capacity, &set) else {
                    continue;
                };
                assert_eq!(
                    payload(&ours),
                    minisketch_bytes(&theirs),
                    "capacity={capacity} count={count} impl={implementation}"
                );
                cases += 1;
            }
        }
    }
    println!("payload comparisons: {cases}");
}

#[test]
fn zero_id_stays_out_of_the_payload() {
    for capacity in [1, 2, 18, 89] {
        let set = ids(capacity as u64, 5);
        let mut with_zero = set.clone();
        with_zero.push(0);
        let theirs = minisketch(0, capacity, &set).unwrap();
        let mut theirs_with_zero = theirs.clone();
        theirs_with_zero.add(0);
        assert_eq!(
            minisketch_bytes(&theirs_with_zero),
            minisketch_bytes(&theirs),
            "minisketch ignores zero"
        );
        assert_eq!(
            payload(&bulk_row(capacity, &with_zero)),
            minisketch_bytes(&theirs),
            "zero membership is kept outside the syndrome payload, capacity={capacity}"
        );
    }
}

#[test]
fn decode_matches_minisketch_within_capacity() {
    let mut cases = 0;
    for capacity in 1..=MAX_CAPACITY {
        for d in 0..=capacity {
            for sample in 0..2u64 {
                let stream = (capacity as u64) << 32 | (d as u64) << 8 | sample;
                let diff = ids(stream, d);
                let (local, remote) = sides(stream, &diff);
                let want = symmetric_difference(&local, &remote);
                let expected = if d == 0 {
                    Row::Equal
                } else {
                    Row::Decoded(want.clone())
                };
                let ours = bulk_row(capacity, &local);
                // Remote bytes produced by minisketch, decoded by bulksketch.
                let remote_bytes = minisketch_bytes(&minisketch(0, capacity, &remote).unwrap());
                assert_eq!(
                    bulk_decode_row(&ours, &remote_bytes),
                    expected,
                    "minisketch remote bytes, capacity={capacity} d={d} sample={sample}"
                );
                // Remote bytes produced by bulksketch.
                assert_eq!(
                    bulk_decode_row(&ours, payload(&bulk_row(capacity, &remote))),
                    expected,
                    "bulksketch remote bytes, capacity={capacity} d={d} sample={sample}"
                );
                for (implementation, theirs) in minisketch_results(capacity, &local, &remote)
                    .into_iter()
                    .enumerate()
                {
                    assert_eq!(
                        theirs.as_ref(),
                        Some(&want),
                        "minisketch impl={implementation} capacity={capacity} d={d}"
                    );
                }
                cases += 1;
            }
        }
    }
    println!("within-capacity cases: {cases}");
}

/// Beyond capacity a sketch can no longer tell every set apart: a set of more
/// than `capacity` IDs can share all syndromes with a different set of at most
/// `capacity` IDs (an alias). Such an alias is unique when it exists. Whatever
/// bulksketch returns must reproduce the sketch exactly: it never returns a set
/// whose syndromes differ from the input. When minisketch finds a set that
/// reproduces the sketch, bulksketch must return the same set.
fn check_over_capacity(capacity: usize, local: &[u64], remote: &[u64], tally: &mut Tally) {
    let want = symmetric_difference(local, remote);
    assert!(want.len() > capacity);
    let sketch_of = |set: &[u64]| minisketch_bytes(&minisketch(0, capacity, set).unwrap());
    let input = sketch_of(&want);
    let ours = bulk_decode_row(
        &bulk_row(capacity, local),
        payload(&bulk_row(capacity, remote)),
    );
    match &ours {
        Row::Equal => {
            assert!(
                input.iter().all(|&b| b == 0),
                "equal reported for nonzero syndromes, capacity={capacity}"
            );
            tally.empty_aliases += 1;
        }
        Row::Decoded(set) => {
            assert!(set.len() <= capacity, "output above budget");
            assert_eq!(
                sketch_of(set),
                input,
                "decoded set does not reproduce the sketch, capacity={capacity} d={}",
                want.len()
            );
            tally.aliases += 1;
            tally.largest_alias_capacity = tally.largest_alias_capacity.max(capacity);
        }
        Row::Failed => tally.failed += 1,
    }
    for theirs in minisketch_results(capacity, local, remote) {
        match theirs {
            None => tally.minisketch_failed += 1,
            Some(set) if sketch_of(&set) == input => {
                // An empty alias means all syndromes cancelled: bulksketch reports Equal.
                let expected = if set.is_empty() {
                    Row::Equal
                } else {
                    Row::Decoded(set)
                };
                assert_eq!(
                    ours, expected,
                    "minisketch found the unique alias, capacity={capacity}"
                );
                tally.minisketch_aliases += 1;
            }
            Some(_) => tally.minisketch_inconsistent += 1,
        }
    }
    tally.cases += 1;
}

#[derive(Debug, Default)]
struct Tally {
    cases: usize,
    failed: usize,
    aliases: usize,
    empty_aliases: usize,
    largest_alias_capacity: usize,
    minisketch_failed: usize,
    minisketch_aliases: usize,
    minisketch_inconsistent: usize,
}

#[test]
fn over_capacity_random_sets_never_decode_inconsistently() {
    let mut tally = Tally::default();
    for capacity in 1..=MAX_CAPACITY {
        for extra in [1, 2, 3, capacity, 2 * capacity] {
            for sample in 0..2u64 {
                let stream = 0x0c << 56 | (capacity as u64) << 32 | (extra as u64) << 8 | sample;
                let (local, remote) = sides(stream, &ids(stream, capacity + extra));
                check_over_capacity(capacity, &local, &remote, &mut tally);
            }
        }
    }
    println!("over capacity, random IDs: {tally:?}");
}

/// Small consecutive integers span low-dimensional GF(2) subspaces, so their
/// syndromes often cancel and aliases are common. This exercises the alias path.
#[test]
fn over_capacity_structured_sets_never_decode_inconsistently() {
    let mut tally = Tally::default();
    for capacity in 1..=MAX_CAPACITY {
        for extra in [1, 2, capacity] {
            let diff: Vec<u64> = (1..=(capacity + extra) as u64).collect();
            let (local, remote) = sides(capacity as u64, &diff);
            check_over_capacity(capacity, &local, &remote, &mut tally);
        }
    }
    println!("over capacity, consecutive IDs: {tally:?}");
}
