fn main() {
    let original = [u64::MAX, 0, 1_u64 << 63, u64::MAX, 7, 3];
    for count in 0..=4 {
        let mut roots = original;
        roots[..count].sort_unstable();
        assert!(roots[..count].is_sorted());
        assert_eq!(roots[count..], original[count..]);
        for word in original[..count].iter() {
            let before = original[..count].iter().filter(|other| *other == word).count();
            let after = roots[..count].iter().filter(|other| *other == word).count();
            assert_eq!(before, after);
        }
        if count == 4 {
            assert_eq!(roots, [0, 1_u64 << 63, u64::MAX, u64::MAX, 7, 3]);
        }
    }
    println!("unsigned sort retained duplicate high words and the original tail for counts 0–4");
}
