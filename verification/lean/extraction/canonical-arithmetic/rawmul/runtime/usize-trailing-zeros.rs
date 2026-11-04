        /// Returns the number of trailing zeros in the binary representation
        /// of `self`.
        ///
        /// # Examples
        ///
        /// ```
        #[doc = concat!("let n = 0b0101000", stringify!($SelfT), ";")]
        /// assert_eq!(n.trailing_zeros(), 3);
        ///
        #[doc = concat!("let zero = 0", stringify!($SelfT), ";")]
        #[doc = concat!("assert_eq!(zero.trailing_zeros(), ", stringify!($BITS), ");")]
        ///
        #[doc = concat!("let max = ", stringify!($SelfT),"::MAX;")]
        #[doc = concat!("assert_eq!(max.trailing_zeros(), 0);")]
        /// ```
        #[stable(feature = "rust1", since = "1.0.0")]
        #[rustc_const_stable(feature = "const_math", since = "1.32.0")]
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline(always)]
        pub const fn trailing_zeros(self) -> u32 {
            return intrinsics::cttz(self);
        }

