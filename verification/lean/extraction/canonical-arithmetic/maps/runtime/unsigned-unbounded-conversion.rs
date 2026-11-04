macro_rules! impl_try_from_unbounded {
    ($source:ty => $($target:ty),+) => {$(
        #[stable(feature = "try_from", since = "1.34.0")]
        #[rustc_const_unstable(feature = "const_convert", issue = "143773")]
        const impl TryFrom<$source> for $target {
            type Error = TryFromIntError;

            /// Tries to create the target number type from a source
            /// number type. This never returns an error.
            #[inline]
            fn try_from(value: $source) -> Result<Self, Self::Error> {
                Ok(value as Self)
            }
        }
    )*}
