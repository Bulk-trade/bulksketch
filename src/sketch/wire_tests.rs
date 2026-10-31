#![forbid(unsafe_code)]

use {
    super::*,
    crate::{BackendRequest, EncodeError, Gf64, ParseError},
    std::sync::Arc,
};

fn limits() -> ParseLimits {
    ParseLimits {
        max_wire_bytes: 100_000,
        max_buckets: 16,
        max_capacity_per_bucket: 89,
        max_total_syndrome_words: 1424,
    }
}

fn record(capacities: &[usize]) -> Vec<u8> {
    let shape = Arc::new(
        SketchShape::<Gf64>::new(
            capacities,
            &ShapeLimits {
                max_wire_bytes: 100_000,
                max_buckets: 16,
                max_capacity_per_bucket: 89,
                max_total_syndrome_words: 1424,
            },
        )
        .unwrap(),
    );
    MutableSketch::new(shape, BackendRequest::Auto)
        .unwrap()
        .freeze()
        .encoded_v1()
        .unwrap()
        .to_vec()
}

#[test]
fn wire_golden_roundtrips() {
    for line in include_str!("../../tests/vectors/core-wire-v1.txt")
        .lines()
        .filter(|l| !l.starts_with('#') && !l.is_empty())
    {
        let (name, hex) = line.split_once(' ').unwrap();
        let bytes: Vec<_> = hex
            .as_bytes()
            .chunks_exact(2)
            .map(|c| u8::from_str_radix(std::str::from_utf8(c).unwrap(), 16).unwrap())
            .collect();
        let view = SketchView::<Gf64>::parse(&bytes, &limits()).unwrap();
        assert_eq!(
            view.as_bytes().as_ptr(),
            bytes.as_ptr(),
            "parse borrows the exact record"
        );
        let frozen = FrozenSketch::from_view(
            view,
            &ShapeLimits {
                max_wire_bytes: 100_000,
                max_buckets: 16,
                max_capacity_per_bucket: 89,
                max_total_syndrome_words: 1424,
            },
        )
        .unwrap();
        let mut mutable = frozen.thaw(BackendRequest::Auto).unwrap();
        mutable.toggle(0);
        mutable.toggle(0);
        let uncached = mutable.freeze();
        let mut dst = vec![0xa5; bytes.len() + 3];
        assert_eq!(uncached.encode_into(&mut dst).unwrap(), bytes.len());
        assert_eq!(&dst[..bytes.len()], bytes, "golden record {name}");
        assert_eq!(
            &dst[bytes.len()..],
            &[0xa5; 3],
            "encoding suffix is untouched"
        );
        assert_eq!(
            uncached.encoded_v1().unwrap(),
            bytes,
            "cached golden record {name}"
        );
        assert_eq!(
            uncached.encoded_v1().unwrap().as_ptr(),
            uncached.encoded_v1().unwrap().as_ptr(),
            "cache reuses the record"
        );
        for len in [0, 23, bytes.len() - 1] {
            let mut short = vec![0x77; len];
            assert_eq!(
                uncached.encode_into(&mut short),
                Err(EncodeError::BufferTooSmall)
            );
            assert!(short.iter().all(|&b| b == 0x77));
        }
    }
}

#[test]
fn wire_precedence_and_canonicality() {
    use ParseError::{InputLimitExceeded, InvalidEncoding};
    let base = record(&[2; 4]);
    check(
        &[0xff],
        &ParseLimits {
            max_wire_bytes: 0,
            ..limits()
        },
        Err(InputLimitExceeded),
    );
    for offset in [0, 4, 5, 6, 7, 10, 11, 20, 21, 22, 23] {
        let mut malformed = base.clone();
        malformed[offset] ^= 0x80;
        check(
            &malformed,
            &ParseLimits {
                max_buckets: 0,
                ..limits()
            },
            Err(InvalidEncoding),
        );
        check(
            &malformed,
            &ParseLimits {
                max_wire_bytes: 0,
                ..limits()
            },
            Err(InputLimitExceeded),
        );
    }
    for count in [0_u16, 3] {
        let mut malformed = base.clone();
        malformed[8..10].copy_from_slice(&count.to_le_bytes());
        check(
            &malformed,
            &ParseLimits {
                max_buckets: 0,
                ..limits()
            },
            Err(InvalidEncoding),
        );
    }
    for offset in [12, 16] {
        let mut malformed = base.clone();
        malformed[offset] ^= 1;
        check(
            &malformed,
            &ParseLimits {
                max_buckets: 0,
                ..limits()
            },
            Err(InvalidEncoding),
        );
    }
    for length in 0..base.len() {
        check(&base[..length], &limits(), Err(InvalidEncoding));
    }
    let mut extra = base.clone();
    extra.push(0);
    check(&extra, &limits(), Err(InvalidEncoding));
    let mut forbidden = base.clone();
    forbidden[32] = 2;
    for caps in [
        ParseLimits {
            max_buckets: 3,
            ..limits()
        },
        ParseLimits {
            max_capacity_per_bucket: 1,
            ..limits()
        },
        ParseLimits {
            max_total_syndrome_words: 7,
            ..limits()
        },
    ] {
        check(&forbidden, &caps, Err(InputLimitExceeded));
    }
    check(&forbidden, &limits(), Err(InvalidEncoding));
    let mut zero_capacity = record(&[1]);
    zero_capacity[24..26].fill(0);
    zero_capacity.truncate(27);
    zero_capacity[16..20].copy_from_slice(&1_u32.to_le_bytes());
    check(&zero_capacity, &limits(), Err(InvalidEncoding));
    zero_capacity[26] = 2;
    check(
        &zero_capacity,
        &ParseLimits {
            max_buckets: 0,
            ..limits()
        },
        Err(InputLimitExceeded),
    );
    check_zero_flags();
}

fn check_zero_flags() {
    use ParseError::InvalidEncoding;
    for buckets in [1, 4, 16] {
        let bytes = record(&vec![1; buckets]);
        let start = 24 + 2 * buckets;
        for bit in 0..buckets.div_ceil(8) * 8 {
            let mut flagged = bytes.clone();
            flagged[start + bit / 8] |= 1 << (bit % 8);
            check(
                &flagged,
                &limits(),
                if bit == 0 {
                    Ok(())
                } else {
                    Err(InvalidEncoding)
                },
            );
        }
        let mut all_bits = bytes;
        all_bits[start + buckets.div_ceil(8)..].fill(0xff);
        check(&all_bits, &limits(), Ok(()));
    }
}

fn check(bytes: &[u8], caps: &ParseLimits, expected: Result<(), ParseError>) {
    assert_eq!(
        SketchView::<Gf64>::parse(bytes, caps).map(|_| ()),
        expected,
        "wire precedence for bytes={bytes:?} limits={caps:?}"
    );
}
