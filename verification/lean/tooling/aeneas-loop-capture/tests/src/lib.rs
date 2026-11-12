#![forbid(unsafe_code)]

pub fn apply(value: u64, power: u32, frobenius: impl Fn(u64, u32) -> u64) -> u64 {
    frobenius(value, power)
}

pub fn captured_callback(value: u64, power: u32, square: impl Fn(u64) -> u64) -> u64 {
    apply(value, power, |mut word, count| {
        for _ in 0..count {
            word = square(word);
        }
        word
    })
}

pub fn aliased_shared_capture(value: u64, power: u32, square: impl Fn(u64) -> u64) -> u64 {
    let first = &square;
    let second = &square;
    apply(value, power, |mut word, count| {
        for bit in 0..count {
            word = if bit & 1 == 0 { first(word) } else { second(word) };
        }
        word
    })
}

pub fn ordinary_shared_loop(input: &u64, count: u32) -> u64 {
    let mut sum = 0;
    for _ in 0..count {
        sum ^= *input;
    }
    sum
}

pub fn captured_phantom_callback<F: Eq, M: Fn(u64, u64) -> u64, S: Fn(u64) -> u64>(
    value: u64,
    power: u32,
    _multiply: M,
    square: S,
) -> u64 {
    apply(value, power, |mut word, count| {
        for _ in 0..count {
            word = square(word);
        }
        word
    })
}

pub fn nested_mutable_shared_capture(input: &(&mut u64,), count: u32) -> u64 {
    let callback = || *input.0;
    let mut sum = 0;
    for _ in 0..count {
        sum ^= callback();
    }
    sum
}

pub fn nested_shared_referent_capture(input: &(&u64,), count: u32) -> u64 {
    let callback = || *input.0;
    let mut sum = 0;
    for _ in 0..count {
        sum ^= callback();
    }
    sum
}

pub trait ReadWord {
    fn word(&self) -> &u64;
}

pub fn captured_borrow_result<T: ReadWord>(value: u64, power: u32, reader: T) -> u64 {
    apply(value, power, |mut word, count| {
        for _ in 0..count {
            word ^= *reader.word();
        }
        word
    })
}

pub fn captured_expandable_referent(input: &Option<(u64, u64)>, count: u32) -> u64 {
    apply(0, count, |mut word, power| {
        for _ in 0..power {
            if let Some((left, right)) = input {
                word ^= *left ^ *right;
            }
        }
        word
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shared_captures_preserve_iteration_and_alias_values() {
        for input in [0, 1, 2, u64::MAX, 0x748dc4cbe3a9915d] {
            for count in 0..33 {
                let expected = if count & 1 == 0 { input } else { input ^ 0x1b };
                assert_eq!(captured_callback(input, count, |word| word ^ 0x1b), expected);
                assert_eq!(aliased_shared_capture(input, count, |word| word ^ 0x1b), expected);
                assert_eq!(captured_phantom_callback::<u8, _, _>(input, count,
                    |left, right| left ^ right, |word| word ^ 0x1b), expected);
                assert_eq!(ordinary_shared_loop(&input, count), if count & 1 == 0 { 0 } else { input });
            }
        }
    }
}
