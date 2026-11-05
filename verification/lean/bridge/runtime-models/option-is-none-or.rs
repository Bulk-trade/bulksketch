    #[inline]
    #[stable(feature = "is_none_or", since = "1.82.0")]
    #[rustc_const_unstable(feature = "const_option_ops", issue = "143956")]
    pub const fn is_none_or(self, f: impl [const] FnOnce(T) -> bool + [const] Destruct) -> bool {
        match self {
            None => true,
            Some(x) => f(x),
        }
    }

