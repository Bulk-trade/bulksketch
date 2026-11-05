macro_rules! impl_try_from_upper_bounded {
    ($source:ty => $($target:ty),+) => {$(
        #[stable(feature = "try_from", since = "1.34.0")]
        #[rustc_const_unstable(feature = "const_convert", issue = "143773")]
        const impl TryFrom<$source> for $target {
            type Error = TryFromIntError;

            /// Tries to create the target number type from a source
            /// number type. This returns an error if the source value
            #[doc = concat!("is greater than [`", stringify!($target), "::MAX`].")]
            #[inline]
            fn try_from(u: $source) -> Result<Self, Self::Error> {
                if u > (Self::MAX as $source) {
                    Err(TryFromIntError(IntErrorKind::PosOverflow))
                } else {
                    Ok(u as Self)
                }
            }
        }
    )*}
}

