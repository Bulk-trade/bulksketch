#[cfg(target_pointer_width = "32")]
mod ptr_try_from_impls {
    use super::{IntErrorKind, TryFromIntError};

    impl_try_from_upper_bounded!(usize => u8, u16);
    impl_try_from_unbounded!(usize => u32, u64, u128);
    impl_try_from_upper_bounded!(usize => i8, i16, i32);
    impl_try_from_unbounded!(usize => i64, i128);

    impl_try_from_both_bounded!(isize => u8, u16);
    impl_try_from_lower_bounded!(isize => u32, u64, u128);
    impl_try_from_both_bounded!(isize => i8, i16);
    impl_try_from_unbounded!(isize => i32, i64, i128);

    rev!(impl_try_from_unbounded, usize => u32);
    rev!(impl_try_from_upper_bounded, usize => u64, u128);
    rev!(impl_try_from_lower_bounded, usize => i8, i16, i32);
    rev!(impl_try_from_both_bounded, usize => i64, i128);

    rev!(impl_try_from_unbounded, isize => u16);
    rev!(impl_try_from_upper_bounded, isize => u32, u64, u128);
    rev!(impl_try_from_unbounded, isize => i32);
    rev!(impl_try_from_both_bounded, isize => i64, i128);
}

#[cfg(target_pointer_width = "64")]
mod ptr_try_from_impls {
    use super::{IntErrorKind, TryFromIntError};

    impl_try_from_upper_bounded!(usize => u8, u16, u32);
    impl_try_from_unbounded!(usize => u64, u128);
    impl_try_from_upper_bounded!(usize => i8, i16, i32, i64);
    impl_try_from_unbounded!(usize => i128);

    impl_try_from_both_bounded!(isize => u8, u16, u32);
    impl_try_from_lower_bounded!(isize => u64, u128);
    impl_try_from_both_bounded!(isize => i8, i16, i32);
    impl_try_from_unbounded!(isize => i64, i128);

    rev!(impl_try_from_unbounded, usize => u32, u64);
    rev!(impl_try_from_upper_bounded, usize => u128);
    rev!(impl_try_from_lower_bounded, usize => i8, i16, i32, i64);
    rev!(impl_try_from_both_bounded, usize => i128);

    rev!(impl_try_from_unbounded, isize => u16, u32);
    rev!(impl_try_from_upper_bounded, isize => u64, u128);
    rev!(impl_try_from_unbounded, isize => i32, i64);
    rev!(impl_try_from_both_bounded, isize => i128);
}
