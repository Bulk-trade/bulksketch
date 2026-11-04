// Pinned nightly-2026-09-17 source excerpts for the explicit std model boundary.

// core/src/array/iter.rs:20-22
pub struct IntoIter<T, const N: usize> {
    inner: ManuallyDrop<InnerSized<T, N>>,
}

// core/src/array/iter.rs:43-80
#[stable(feature = "array_into_iter_impl", since = "1.53.0")]
impl<T, const N: usize> IntoIterator for [T; N] {
    type Item = T;
    type IntoIter = IntoIter<T, N>;

    /// Creates a consuming iterator, that is, one that moves each value out of
    /// the array (from start to end).
    ///
    /// The array cannot be used after calling this unless `T` implements
    /// `Copy`, so the whole array is copied.
    ///
    /// Arrays have special behavior when calling `.into_iter()` prior to the
    /// 2021 edition -- see the [array] Editions section for more information.
    ///
    /// [array]: prim@array
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        // SAFETY: The transmute here is actually safe. The docs of `MaybeUninit`
        // promise:
        //
        // > `MaybeUninit<T>` is guaranteed to have the same size and alignment
        // > as `T`.
        //
        // The docs even show a transmute from an array of `MaybeUninit<T>` to
        // an array of `T`.
        //
        // With that, this initialization satisfies the invariants.
        //
        // FIXME: If normal `transmute` ever gets smart enough to allow this
        // directly, use it instead of `transmute_unchecked`.
        let data: [MaybeUninit<T>; N] = unsafe { transmute_unchecked(self) };
        // SAFETY: The original array was entirely initialized and the alive
        // range we're passing here represents that fact.
        let inner = unsafe { InnerSized::new_unchecked(IndexRange::zero_to(N), data) };
        IntoIter { inner: ManuallyDrop::new(inner) }
    }
}


// core/src/array/iter.rs:241-247
impl<T, const N: usize> Iterator for IntoIter<T, N> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.unsize_mut().next()
    }

// core/src/array/iter/iter_inner.rs:206-220
    pub(super) fn next(&mut self) -> Option<T> {
        // Get the next index from the front.
        //
        // Increasing `alive.start` by 1 maintains the invariant regarding
        // `alive`. However, due to this change, for a short time, the alive
        // zone is not `data[alive]` anymore, but `data[idx..alive.end]`.
        self.alive.next().map(|idx| {
            // Read the element from the array.
            // SAFETY: `idx` is an index into the former "alive" region of the
            // array. Reading this element means that `data[idx]` is regarded as
            // dead now (i.e. do not touch). As `idx` was the start of the
            // alive-zone, the alive zone is now `data[alive]` again, restoring
            // all invariants.
            unsafe { self.data.get_unchecked(idx).assume_init_read() }
        })
