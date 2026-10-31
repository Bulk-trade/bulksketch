//! Copy-on-write algebra with immutable snapshots and generation-local encoding caches.
#![forbid(unsafe_code)]

use {
    super::{
        dispatch::InsertDispatch,
        scratch::InsertScratch,
        shape::{ShapeLimits, SketchShape},
        wire::{SketchView, encode},
    },
    crate::{
        backend::detect,
        field::BinaryField,
        types::{
            BackendError, BackendRequest, CreateError, EncodeError, ShapeError, ShapeMismatch,
            UpdateError,
        },
    },
    std::sync::{Arc, OnceLock},
};

#[derive(Debug)]
pub(crate) struct State<F: BinaryField> {
    pub(crate) shape: Arc<SketchShape<F>>,
    pub(crate) words: Vec<u64>,
    pub(crate) zero_words: Vec<u64>,
    pub(crate) encoded_v1: OnceLock<Arc<[u8]>>,
}

impl<F: BinaryField> Clone for State<F> {
    fn clone(&self) -> Self {
        Self {
            shape: Arc::clone(&self.shape),
            words: self.words.clone(),
            zero_words: self.zero_words.clone(),
            encoded_v1: OnceLock::new(),
        }
    }
}

/// Parity sketch. Clones share immutable state until their first mutation.
#[derive(Clone, Debug)]
pub struct MutableSketch<F: BinaryField> {
    state: Arc<State<F>>,
    insert_dispatch: InsertDispatch<F>,
}

impl<F: BinaryField> MutableSketch<F> {
    /// Allocate empty algebra for an already admitted shape and resolve insertion once.
    ///
    /// # Errors
    /// The requested backend is unavailable or algebra storage cannot be reserved.
    #[inline]
    pub fn new(shape: Arc<SketchShape<F>>, backend: BackendRequest) -> Result<Self, CreateError> {
        let insert_dispatch =
            InsertDispatch::new(detect::resolve(backend).map_err(CreateError::Backend)?);
        let allocate = |len| {
            let mut words = Vec::new();
            words
                .try_reserve_exact(len)
                .map_err(|_| CreateError::AllocationFailed)?;
            words.resize(len, 0);
            Ok::<_, CreateError>(words)
        };
        let words = allocate(shape.total_syndrome_words())?;
        let zero_words = allocate(shape.bucket_count().div_ceil(64))?;
        Ok(Self {
            state: Arc::new(State {
                shape,
                words,
                zero_words,
                encoded_v1: OnceLock::new(),
            }),
            insert_dispatch,
        })
    }

    /// Toggle one original ID, including zero. Two toggles cancel.
    #[inline]
    pub fn toggle(&mut self, id: u64) {
        let operation = self.insert_dispatch.toggle;
        let state = self.mutate();
        operation(&state.shape, &mut state.words, &mut state.zero_words, id);
    }

    /// Partition this call's arrivals once and toggle each row in arrival order.
    ///
    /// # Errors
    /// Insertion scratch is short; the sketch and cached encoding remain unchanged.
    pub fn toggle_batch(
        &mut self,
        ids: &[u64],
        scratch: &mut InsertScratch,
    ) -> Result<(), UpdateError> {
        if !scratch.covers(ids.len(), self.state.shape.bucket_count()) {
            return Err(UpdateError::ScratchTooSmall);
        }
        let operation = self.insert_dispatch.batch;
        let state = self.mutate();
        operation(
            &state.shape,
            &mut state.words,
            &mut state.zero_words,
            ids,
            scratch,
        );
        Ok(())
    }

    /// XOR algebra and zero membership from exactly the same shape.
    ///
    /// # Errors
    /// A shape mismatch leaves the state and cached encoding unchanged.
    pub fn xor_assign(&mut self, other: &FrozenSketch<F>) -> Result<(), ShapeMismatch> {
        if self.state.shape != other.state.shape {
            return Err(ShapeMismatch);
        }
        let operation = self.insert_dispatch.xor;
        let state = self.mutate();
        operation(&mut state.words, &other.state.words);
        operation(&mut state.zero_words, &other.state.zero_words);
        Ok(())
    }

    /// Snapshot the current generation in constant time.
    #[must_use]
    pub fn freeze(&self) -> FrozenSketch<F> {
        FrozenSketch {
            state: Arc::clone(&self.state),
        }
    }

    fn mutate(&mut self) -> &mut State<F> {
        let state = Arc::make_mut(&mut self.state);
        // A populated cache can outlive every snapshot; unique ownership still needs invalidation.
        state.encoded_v1.take();
        state
    }
}

/// Immutable, cheaply cloned state. Backend identity is deliberately absent.
#[derive(Clone, Debug)]
pub struct FrozenSketch<F: BinaryField> {
    pub(crate) state: Arc<State<F>>,
}

impl<F: BinaryField> FrozenSketch<F> {
    /// Share this immutable generation until the mutable handle first changes it.
    ///
    /// # Errors
    /// The requested insertion backend is unavailable in this build or on this CPU/OS.
    #[inline]
    pub fn thaw(&self, backend: BackendRequest) -> Result<MutableSketch<F>, BackendError> {
        Ok(MutableSketch {
            state: Arc::clone(&self.state),
            insert_dispatch: InsertDispatch::new(detect::resolve(backend)?),
        })
    }

    /// Borrow this generation's cached canonical record.
    ///
    /// # Errors
    /// Record storage cannot be reserved.
    ///
    /// # Panics
    /// Only if the internally validated record size is inconsistent.
    pub fn encoded_v1(&self) -> Result<&[u8], EncodeError> {
        if let Some(bytes) = self.state.encoded_v1.get() {
            return Ok(bytes);
        }
        let mut bytes = Vec::new();
        let len = self.shape().wire_bytes();
        bytes
            .try_reserve_exact(len)
            .map_err(|_| EncodeError::AllocationFailed)?;
        bytes.resize(len, 0);
        self.encode_into(&mut bytes)?;
        // Concurrent readers may finish first; either canonical encoding is identical.
        let _ = self.state.encoded_v1.set(Arc::from(bytes));
        Ok(self.state.encoded_v1.get().expect("encoding initialized"))
    }

    /// Write one complete canonical record; leave any destination suffix untouched.
    ///
    /// # Errors
    /// A short destination is rejected before any write.
    pub fn encode_into(&self, dst: &mut [u8]) -> Result<usize, EncodeError> {
        encode::encode_into(self.shape(), &self.state.words, &self.state.zero_words, dst)
    }

    /// Allocate an owned immutable snapshot only after wire and shape admission.
    /// Owned import of a parsed view; no arithmetic or decode runs here.
    ///
    /// # Errors
    /// The supplied shape/storage limits are stricter than the parsed view's dimensions.
    ///
    /// # Panics
    /// Only if the validated view violates its internal dimension/word invariants.
    pub fn from_view(view: SketchView<'_, F>, limits: &ShapeLimits) -> Result<Self, ShapeError> {
        // Check caller storage caps before allocating even the temporary descriptors.
        if view.bucket_count() > limits.max_buckets
            || view.as_bytes().len() > limits.max_wire_bytes
            || view.total_syndrome_words() > limits.max_total_syndrome_words
            || (0..view.bucket_count())
                .any(|b| view.capacity(b).expect("validated row") > limits.max_capacity_per_bucket)
        {
            return Err(ShapeError::InputLimitExceeded);
        }
        let capacities: Vec<_> = (0..view.bucket_count())
            .map(|b| view.capacity(b).expect("validated row"))
            .collect();
        let shape = Arc::new(SketchShape::new(&capacities, limits)?);
        let words = view
            .syndrome_bytes()
            .chunks_exact(8)
            .map(|w| u64::from_le_bytes(w.try_into().expect("validated GF64 word")))
            .collect();
        let mut zero_words = vec![0; shape.bucket_count().div_ceil(64)];
        zero_words[0] = u64::from(view.zero(0).expect("validated row zero"));
        let encoded_v1 = OnceLock::from(Arc::from(view.as_bytes()));
        Ok(Self {
            state: Arc::new(State {
                shape,
                words,
                zero_words,
                encoded_v1,
            }),
        })
    }

    /// Validated fixed identity/modulo layout.
    #[must_use]
    pub fn shape(&self) -> &SketchShape<F> {
        &self.state.shape
    }
}
