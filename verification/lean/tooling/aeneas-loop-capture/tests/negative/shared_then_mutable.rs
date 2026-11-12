pub fn alias(value: &mut u64) -> u64 {
    let shared = &*value;
    let mutable = &mut *value;
    *mutable ^= 1;
    *shared
}
