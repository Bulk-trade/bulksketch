#![forbid(unsafe_code)]

use bulksketch::{
    BackendError, BackendId, BackendRequest, DecodeError, Decoder, Gf64, ParseError, ShapeError,
};

fn check_error<E: std::error::Error + Clone + Copy + Eq + Send + Sync>(error: E, expected: &str) {
    assert_eq!(error.to_string(), expected);
    assert!(error.source().is_none());
}

#[test]
fn value_error_contracts() {
    let _: fn(BackendRequest, u64) -> Result<Decoder<Gf64>, BackendError> = Decoder::new;
    for (error, message) in [
        (DecodeError::ShapeMismatch, "sketch shapes differ"),
        (
            DecodeError::InvalidPlan,
            "invalid decode plan or output budget",
        ),
        (
            DecodeError::CandidateLimitExceeded,
            "candidate input limit exceeded",
        ),
        (DecodeError::WorkLimitExceeded, "decode work limit exceeded"),
        (DecodeError::ScratchTooSmall, "decode scratch is too small"),
    ] {
        check_error(error, message);
    }
    for (error, message) in [
        (ShapeError::InvalidShape, "invalid sketch shape"),
        (ShapeError::InputLimitExceeded, "shape input limit exceeded"),
    ] {
        check_error(error, message);
    }
    for (error, message) in [
        (ParseError::InputLimitExceeded, "wire input limit exceeded"),
        (ParseError::InvalidEncoding, "invalid sketch encoding"),
    ] {
        check_error(error, message);
    }
    for (backend, message) in [
        (BackendId::Portable, "backend Portable is unavailable"),
        (BackendId::Pclmul, "backend Pclmul is unavailable"),
        (BackendId::Vpclmul256, "backend Vpclmul256 is unavailable"),
        (BackendId::Vpclmul512, "backend Vpclmul512 is unavailable"),
    ] {
        check_error(BackendError(backend), message);
    }
}
