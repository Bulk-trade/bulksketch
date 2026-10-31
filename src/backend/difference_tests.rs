//! Fused Compare kernel: immutable inputs, every byte alignment and bounded tails.
#![forbid(unsafe_code)]
use {
    super::{contract::BulkKernels, portable::Portable},
    crate::field::Gf64,
};
fn check<K: BulkKernels<Gf64>>() {
    for c in (0..=100).chain([1424]) {
        for offset in 0..64 {
            let local: Vec<_> = (0..c)
                .map(|i| (i as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15))
                .collect();
            let mut bytes = vec![0xa5; 8 * c + offset + 8];
            for (word, &value) in bytes[offset..offset + 8 * c]
                .chunks_exact_mut(8)
                .zip(&local)
            {
                word.copy_from_slice(&value.to_le_bytes());
            }
            for changed in [None, c.checked_sub(1), (c > 0).then_some(0)] {
                let mut remote = bytes.clone();
                if let Some(i) = changed {
                    remote[offset + 8 * i + 7] ^= 0x80;
                }
                let expected: Vec<_> = local
                    .iter()
                    .zip(remote[offset..offset + 8 * c].chunks_exact(8))
                    .map(|(&a, b)| a ^ u64::from_le_bytes(b.try_into().unwrap()))
                    .collect();
                let mut actual = vec![u64::MAX; c + 2];
                assert_eq!(
                    K::difference(&mut actual[1..=c], &local, &remote[offset..offset + 8 * c]),
                    expected.iter().any(|&x| x != 0),
                    "zero scan c={c} offset={offset}"
                );
                assert_eq!(actual[1..=c], expected, "difference c={c} offset={offset}");
                assert_eq!((actual[0], actual[c + 1]), (u64::MAX, u64::MAX));
                assert_eq!(&bytes[..offset], &remote[..offset]);
            }
        }
    }
}
#[test]
fn difference_all_words_and_byte_alignments() {
    check::<Portable>();
    #[cfg(target_arch = "x86_64")]
    if super::detect::resolve(crate::types::BackendRequest::Force(
        crate::types::BackendId::Vpclmul512,
    ))
    .is_ok()
    {
        check::<super::x86_vpclmul512::Vpclmul512>();
    }
}
