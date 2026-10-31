//! Value-only definitions; this module has no dependency on the engine layers.
#![forbid(unsafe_code)]

/// Polynomial-basis identity, including the irreducible polynomial.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum FieldId {
    /// GF(2^64), modulus Z^64 + Z^4 + Z^3 + Z + 1, bit i is Z^i.
    Gf64 = 1,
}

/// Shape admission failure, before any row storage is allocated.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ShapeError {
    /// Unsupported field, zero/non-power-of-two row count, or zero capacity.
    InvalidShape,
    /// Configured storage/dimension cap or representable wire dimension exceeded.
    InputLimitExceeded,
}

/// Bounded wire admission failure. No view is exposed on either error.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ParseError {
    /// A caller-supplied byte or dimension limit was exceeded.
    InputLimitExceeded,
    /// Unknown metadata, malformed lengths, or noncanonical payload.
    InvalidEncoding,
}

impl std::fmt::Display for ShapeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::InvalidShape => "invalid sketch shape",
            Self::InputLimitExceeded => "shape input limit exceeded",
        })
    }
}
impl std::error::Error for ShapeError {}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::InputLimitExceeded => "wire input limit exceeded",
            Self::InvalidEncoding => "invalid sketch encoding",
        })
    }
}
impl std::error::Error for ParseError {}

/// Runtime arithmetic capability. No complete-operation dispatch lives in this type.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BackendId {
    /// Always-available safe Rust arithmetic.
    Portable,
    /// Scalar x86 carryless multiplication.
    Pclmul,
    /// 256-bit vector carryless multiplication, with CPU and OS state checked.
    Vpclmul256,
    /// 512-bit vector carryless multiplication, with CPU and OS state checked.
    Vpclmul512,
}

/// Backend selection requested at engine construction, before any decode.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BackendRequest {
    /// Select from capabilities detected at runtime.
    Auto,
    /// Require this capability; never bypass feature/OS-state validation.
    Force(BackendId),
}

/// An explicitly requested backend is unavailable in this build or on this CPU/OS.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BackendError(pub BackendId);

/// Construction of mutable state failed before any state was returned.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CreateError {
    /// The requested arithmetic implementation is unavailable.
    Backend(BackendError),
    /// The algebraic buffers could not be reserved.
    AllocationFailed,
}

/// Batch insertion failed before changing the sketch.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UpdateError {
    /// The supplied insertion arena cannot hold this call's IDs or row offsets.
    ScratchTooSmall,
}

/// XOR requires identical fields, row counts and capacities.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ShapeMismatch;

/// Encoding failed without changing the destination or algebraic state.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EncodeError {
    /// The destination cannot hold the complete record.
    BufferTooSmall,
    /// The cached record could not be reserved.
    AllocationFailed,
}

impl std::fmt::Display for CreateError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Backend(error) => error.fmt(f),
            Self::AllocationFailed => f.write_str("sketch allocation failed"),
        }
    }
}
impl std::error::Error for CreateError {}
impl std::fmt::Display for UpdateError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("insertion scratch is too small")
    }
}
impl std::error::Error for UpdateError {}
impl std::fmt::Display for ShapeMismatch {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("sketch shapes differ")
    }
}
impl std::error::Error for ShapeMismatch {}
impl std::fmt::Display for EncodeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::BufferTooSmall => "encoding buffer is too small",
            Self::AllocationFailed => "encoding allocation failed",
        })
    }
}
impl std::error::Error for EncodeError {}

impl std::fmt::Display for BackendError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "backend {:?} is unavailable", self.0)
    }
}
impl std::error::Error for BackendError {}

/// Backend-independent logical work, never elapsed time or instruction count.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct WorkUnits(pub u64);

/// A request-wide failure publishes no row report or provisional IDs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DecodeError {
    /// Local and remote fields, row counts or capacities differ.
    ShapeMismatch,
    /// Unknown plan or an output budget larger than any row capacity.
    InvalidPlan,
    /// Raw candidate count exceeds the request cap, before normalization.
    CandidateLimitExceeded,
    /// Work arithmetic overflows or the next charge exceeds the request limit.
    WorkLimitExceeded,
    /// Layout overflows, exceeds its byte cap, or any supplied segment is short.
    ScratchTooSmall,
}

/// An admitted row failed algebraically; independently successful rows remain usable.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DecodeFailure {
    /// Zero consumes an unavailable slot, or locator/final output exceeds beta.
    DegreeExceedsBudget,
    /// The locator fails required canonicality/algebraic validation.
    InvalidLocator,
    /// The locator does not split into distinct permitted field roots.
    NotSplit,
    /// Re-encoding fails any stored odd syndrome or the zero channel.
    VerificationFailed,
}

impl std::fmt::Display for DecodeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::ShapeMismatch => "sketch shapes differ",
            Self::InvalidPlan => "invalid decode plan or output budget",
            Self::CandidateLimitExceeded => "candidate input limit exceeded",
            Self::WorkLimitExceeded => "decode work limit exceeded",
            Self::ScratchTooSmall => "decode scratch is too small",
        })
    }
}
impl std::error::Error for DecodeError {}

/// Deterministic stage order. Repeated trace/GCD/division/leaf stages follow factor traversal.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Stage {
    /// Propose the nonzero root S1 before general decoding.
    DirectOne,
    /// Derive a distinct nonzero pair from S1 and S3 before general decoding.
    DirectTwo,
    /// Reject inconsistent cubic prefixes before inversion (V3).
    GuardThree,
    /// Normalize a passed cubic Newton guard (V3).
    NewtonThree,
    /// Reject inconsistent quartic prefixes before inversion (V3).
    GuardFour,
    /// Normalize a passed quartic Newton guard (V3).
    NewtonFour,
    /// Propose the roots of a cubic factor (V3).
    LeafThree,
    /// Propose the roots of a quartic factor (V3).
    LeafFour,
    /// Certify a complete distinct nonzero factor root set (V3).
    FactorVerification,
    /// Expand odd syndromes and reconstruct even powers.
    Reconstruction,
    /// Binary Berlekamp-Massey iterations.
    BerlekampMassey,
    /// Evaluate the original locator at normalized hints.
    CandidateEvaluation,
    /// Divide out confirmed candidate roots.
    Deflation,
    /// Build a factor's modular-square table.
    ReducerPreparation,
    /// Find the least affine multiple and solve its binary map (V3).
    AffinePreparation,
    /// Enumerate and evaluate the recovered affine solution coset (V3).
    AffineEnumeration,
    /// Form an annihilator splitter for the current affine coset (V3).
    AffineSplit,
    /// Try the next canonical trace direction and the internal split check.
    Trace,
    /// Compute a monic polynomial GCD.
    Gcd,
    /// Divide a factor exactly after a proper split.
    FactorDivision,
    /// Solve degree-one or degree-two leaves.
    Leaf,
    /// Verify every stored odd syndrome by re-encoding or rebuilt recurrence.
    Verification,
    /// Sort and validate the final original IDs.
    Canonicalization,
}

/// Public stage progress contains no row outcome or provisional ID.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StageProgress {
    /// A deterministic stage completed; counters are cumulative for the request.
    Completed {
        /// Bucket whose stage completed, in deterministic request traversal order.
        bucket: usize,
        /// Stage just executed.
        stage: Stage,
        /// Logical work consumed so far.
        work: WorkUnits,
        /// Peak required workspace bytes, excluding unused arena capacity.
        peak_scratch_bytes: usize,
        /// Original BM locator degree for this row; zero until BM completes.
        locator_degree: usize,
        /// Confirmed candidate roots so far in this row.
        candidate_hits: usize,
        /// Trace directions attempted so far in this row.
        trace_attempts: usize,
        /// Degree returned by this row's most recent GCD; zero before the first GCD.
        gcd_degree: usize,
    },
    /// Terminal request failure; finishing the job must return this error.
    Failed(DecodeError),
}

/// Internal arithmetic product, distinct from a canonical field element.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct RawProduct {
    pub(crate) lo: u64,
    pub(crate) hi: u64,
}

/// One request meter, shared by preprocessing and all rows. A failed charge is terminal.
#[derive(Debug)]
pub(crate) struct WorkMeter {
    limit: WorkUnits,
    used: WorkUnits,
    exhausted: bool,
}

impl WorkMeter {
    pub(crate) fn new(limit: WorkUnits) -> Self {
        Self {
            limit,
            used: WorkUnits(0),
            exhausted: false,
        }
    }

    pub(crate) fn charge(&mut self, charge: WorkUnits) -> Result<(), DecodeError> {
        let next = self.used.0.checked_add(charge.0);
        if self.exhausted || next.is_none_or(|n| n > self.limit.0) {
            self.exhausted = true;
            return Err(DecodeError::WorkLimitExceeded);
        }
        self.used = WorkUnits(next.expect("checked work charge"));
        Ok(())
    }

    pub(crate) fn used(&self) -> WorkUnits {
        self.used
    }
}

#[cfg(test)]
pub(crate) mod small_degree_observer;
