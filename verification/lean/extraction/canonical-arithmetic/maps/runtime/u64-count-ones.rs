        pub const BITS: u32 = Self::MAX.count_ones();

        /// Returns the number of ones in the binary representation of `self`.
        ///
        /// # Examples
        ///
        /// ```
        #[doc = concat!("let n = 0b01001100", stringify!($SelfT), ";")]
        /// assert_eq!(n.count_ones(), 3);
        ///
        #[doc = concat!("let max = ", stringify!($SelfT),"::MAX;")]
        #[doc = concat!("assert_eq!(max.count_ones(), ", stringify!($BITS), ");")]
        ///
        #[doc = concat!("let zero = 0", stringify!($SelfT), ";")]
        /// assert_eq!(zero.count_ones(), 0);
        /// ```
        #[stable(feature = "rust1", since = "1.0.0")]
        #[rustc_const_stable(feature = "const_math", since = "1.32.0")]
        #[doc(alias = "popcount")]
        #[doc(alias = "popcnt")]
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline(always)]
        pub const fn count_ones(self) -> u32 {
            return intrinsics::ctpop(self);
        }
