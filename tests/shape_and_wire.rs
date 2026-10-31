use bulksketch::{
    BinaryField, FieldId, Gf64, ParseError, ParseLimits, ShapeError, ShapeLimits, SketchShape,
    SketchView,
};

fn shape_limits() -> ShapeLimits {
    ShapeLimits {
        max_wire_bytes: 1_000_000,
        max_buckets: 16,
        max_capacity_per_bucket: 89,
        max_total_syndrome_words: 16 * 89,
    }
}

fn parse_limits() -> ParseLimits {
    let l = shape_limits();
    ParseLimits {
        max_wire_bytes: l.max_wire_bytes,
        max_buckets: l.max_buckets,
        max_capacity_per_bucket: l.max_capacity_per_bucket,
        max_total_syndrome_words: l.max_total_syndrome_words,
    }
}

fn vectors() -> Vec<(&'static str, Vec<u8>)> {
    include_str!("vectors/core-wire-v1.txt")
        .lines()
        .filter(|l| !l.starts_with('#') && !l.is_empty())
        .map(|line| {
            let (name, hex) = line.split_once(' ').unwrap();
            let bytes = hex
                .as_bytes()
                .chunks_exact(2)
                .map(|pair| u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16).unwrap())
                .collect();
            (name, bytes)
        })
        .collect()
}

#[test]
fn shape_identity_and_storage() {
    let limits = shape_limits();
    let shape = SketchShape::<Gf64>::new(&[1, 2], &limits).unwrap();
    assert_eq!(shape.capacities(), &[1, 2]);
    assert_eq!(shape.total_syndrome_words(), 3);
    assert_eq!(
        shape.wire_bytes(),
        53,
        "24 header + 4 descriptors + 1 zero byte + 24 syndromes"
    );
    assert_eq!(shape.bucket_count(), 2);
    for id in [0, 1, 2, 1 << 63, u64::MAX] {
        assert_eq!(
            shape.bucket_for(id),
            (id % 2) as usize,
            "identity routing retains every bit"
        );
        assert!(shape.permits_id((id % 2) as usize, id));
        assert!(!shape.permits_id(2, id));
        assert!(!shape.permits_id(1 - (id % 2) as usize, id));
    }
    for bad in [&[][..], &[1, 1, 1][..], &[0][..]] {
        assert_eq!(
            SketchShape::<Gf64>::new(bad, &limits).unwrap_err(),
            ShapeError::InvalidShape
        );
    }
    for restricted in [
        ShapeLimits {
            max_wire_bytes: 52,
            ..limits
        },
        ShapeLimits {
            max_buckets: 1,
            ..limits
        },
        ShapeLimits {
            max_capacity_per_bucket: 1,
            ..limits
        },
        ShapeLimits {
            max_total_syndrome_words: 2,
            ..limits
        },
    ] {
        assert_eq!(
            SketchShape::<Gf64>::new(&[1, 2], &restricted).unwrap_err(),
            ShapeError::InputLimitExceeded
        );
    }
    assert!(SketchShape::<Gf64>::new(&[usize::MAX], &limits).is_err());
    assert!(SketchShape::<Gf64>::new(&[1], &limits).is_ok());
    assert_eq!(
        (Gf64::BITS, Gf64::MODULUS_LOW, Gf64::MASK, Gf64::WIRE_ID),
        (64, 0x1b, u64::MAX, FieldId::Gf64)
    );
}

#[test]
fn wire_golden_views() {
    let fixtures = vectors();
    let limits = parse_limits();
    for (name, bytes) in &fixtures {
        let view = SketchView::<Gf64>::parse(bytes, &limits).unwrap();
        assert_eq!(view.as_bytes(), bytes);
        assert_eq!(view.bucket_count(), 2);
        assert_eq!(view.total_syndrome_words(), 2);
        assert_eq!(view.capacity(0), Some(1));
        assert_eq!(view.capacity(1), Some(1));
        assert_eq!(view.capacity(2), None);
        assert_eq!(view.zero(0), Some(*name == "zero"));
        assert_eq!(view.zero(1), Some(false));
        assert_eq!(view.zero(2), None);
        assert_eq!(view.odd_syndrome(0, 0), Some(0));
        assert_eq!(
            view.odd_syndrome(1, 0),
            Some(if *name == "top" { 1 << 63 } else { 0 })
        );
        assert_eq!(view.odd_syndrome(1, 1), None);
        assert_eq!(view.odd_syndrome(2, 0), None);
    }
}

#[test]
fn parser_failure_precedence() {
    let limits = parse_limits();
    let good = &vectors()[0].1;
    let error = |b: &[u8], l: &ParseLimits| SketchView::<Gf64>::parse(b, l).unwrap_err();
    let short = ParseLimits {
        max_wire_bytes: 0,
        ..limits
    };
    assert_eq!(error(b"bad", &short), ParseError::InputLimitExceeded);
    let no_rows = ParseLimits {
        max_buckets: 0,
        ..limits
    };
    for offset in [0, 4, 5, 6, 7, 10, 11, 12, 16, 20, 21, 22, 23] {
        let mut malformed = good.clone();
        malformed[offset] ^= 0x80;
        assert_eq!(
            error(&malformed, &no_rows),
            ParseError::InvalidEncoding,
            "fixed metadata before row cap, offset {offset}"
        );
    }
    let mut forbidden_zero = good.clone();
    forbidden_zero[28] = 2;
    assert_eq!(
        error(&forbidden_zero, &no_rows),
        ParseError::InputLimitExceeded
    );
    assert_eq!(
        error(&forbidden_zero, &limits),
        ParseError::InvalidEncoding,
        "only original ID zero in row zero is representable"
    );
    forbidden_zero[28] = 0x80;
    assert_eq!(
        error(&forbidden_zero, &limits),
        ParseError::InvalidEncoding,
        "unused zero padding is canonical"
    );
    let no_words = ParseLimits {
        max_total_syndrome_words: 0,
        ..limits
    };
    assert_eq!(
        error(&forbidden_zero, &no_words),
        ParseError::InputLimitExceeded
    );
    let no_capacity = ParseLimits {
        max_capacity_per_bucket: 0,
        ..limits
    };
    assert_eq!(
        error(&forbidden_zero, &no_capacity),
        ParseError::InputLimitExceeded
    );
    let mut zero_capacity = good.clone();
    zero_capacity[24] = 0;
    assert_eq!(error(&zero_capacity, &limits), ParseError::InvalidEncoding);
    for len in 0..good.len() {
        assert!(
            SketchView::<Gf64>::parse(&good[..len], &limits).is_err(),
            "truncated input length {len}"
        );
    }
}
