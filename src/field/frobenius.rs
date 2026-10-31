//! Fixed GF64 linear maps shared by insertion and the Itoh–Tsujii chain.
#![forbid(unsafe_code)]

const POWERS: [u32; 9] = [1, 2, 3, 4, 5, 6, 7, 15, 31];
pub(crate) static TABLES: [[[u64; 16]; 16]; 9] = tables();

#[inline]
pub(crate) fn lookup(word: u64, power: u32) -> Option<u64> {
    let index = match power {
        1..=7 => usize::try_from(power - 1).expect("small map index"),
        15 => 7,
        31 => 8,
        _ => return None,
    };
    let mut result = 0;
    for (nibble, entries) in TABLES[index].iter().enumerate() {
        result ^= entries[usize::try_from((word >> (4 * nibble)) & 15).expect("nibble index")];
    }
    Some(result)
}

/// The eight-multiply inverse chain also needs the 21st Frobenius power.
#[inline]
pub(crate) fn inverse21(word: u64) -> u64 {
    static TABLE: [[u64; 16]; 16] = inverse21_table();
    let mut result = 0;
    for (nibble, entries) in TABLE.iter().enumerate() {
        result ^= entries[usize::try_from((word >> (4 * nibble)) & 15).expect("nibble index")];
    }
    result
}

const fn inverse21_table() -> [[u64; 16]; 16] {
    let mut table = [[0; 16]; 16];
    let mut bit = 0;
    while bit < 64 {
        let mut column = 1_u64 << bit;
        let mut power = 0;
        while power < 21 {
            column = square(column);
            power += 1;
        }
        let mut value = 0;
        while value < 16 {
            if value & (1 << (bit % 4)) != 0 {
                table[bit / 4][value] ^= column;
            }
            value += 1;
        }
        bit += 1;
    }
    table
}

pub(crate) const fn square(word: u64) -> u64 {
    let mut square = 0_u128;
    let mut bit = 0;
    while bit < 64 {
        if word & (1_u64 << bit) != 0 {
            square ^= 1_u128 << (2 * bit);
        }
        bit += 1;
    }
    let polynomial = (1_u128 << 64) | 0x1b;
    bit = 128;
    while bit > 64 {
        bit -= 1;
        if square & (1_u128 << bit) != 0 {
            square ^= polynomial << (bit - 64);
        }
    }
    // The long division above leaves exactly one canonical field word.
    let bytes = square.to_le_bytes();
    u64::from_le_bytes([
        bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
    ])
}

#[expect(
    clippy::large_stack_arrays,
    reason = "only evaluated at compile time to initialize immutable static maps"
)]
const fn tables() -> [[[u64; 16]; 16]; 9] {
    let mut tables = [[[0; 16]; 16]; 9];
    let mut columns = [0_u64; 64];
    let mut bit = 0;
    while bit < 64 {
        columns[bit] = 1 << bit;
        bit += 1;
    }
    let mut index = 0;
    let mut power = 0;
    while index < POWERS.len() {
        while power < POWERS[index] {
            bit = 0;
            while bit < 64 {
                columns[bit] = square(columns[bit]);
                bit += 1;
            }
            power += 1;
        }
        let mut nibble = 0;
        while nibble < 16 {
            let mut value: usize = 1;
            while value < 16 {
                tables[index][nibble][value] = tables[index][nibble][value & (value - 1)]
                    ^ columns[4 * nibble + value.trailing_zeros() as usize];
                value += 1;
            }
            nibble += 1;
        }
        index += 1;
    }
    tables
}

#[cfg(test)]
mod tests {
    use {
        super::{POWERS, TABLES, lookup},
        crate::field::{Gf64, gf64},
    };

    #[test]
    fn fixed_frobenius_maps_match_scalar_regeneration() {
        for power in POWERS {
            for word in (0..64)
                .map(|bit| 1_u64 << bit)
                .chain((0_u64..4096).map(|mut word| {
                    word = word.wrapping_add(0x9e37_79b9_7f4a_7c15);
                    word = (word ^ (word >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
                    word = (word ^ (word >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
                    word ^ (word >> 31)
                }))
            {
                let mut expected = word;
                for _ in 0..power {
                    expected = gf64::square::<Gf64>(expected);
                }
                assert_eq!(
                    lookup(word, power),
                    Some(expected),
                    "power={power} word={word:#x}"
                );
            }
            for (nibble, entries) in TABLES[match power {
                15 => 7,
                31 => 8,
                _ => usize::try_from(power - 1).unwrap(),
            }]
            .iter()
            .enumerate()
            {
                for (value, &actual) in entries.iter().enumerate() {
                    let mut expected = u64::try_from(value).unwrap() << (4 * nibble);
                    for _ in 0..power {
                        expected = gf64::square::<Gf64>(expected);
                    }
                    assert_eq!(
                        actual, expected,
                        "table power={power} nibble={nibble} value={value}"
                    );
                }
            }
        }
        for power in [0, 8, 14, 16, 30, 32, 63, 64] {
            assert_eq!(lookup(u64::MAX, power), None);
        }
        println!(
            "SHARED FROBENIUS TABLE BYTES {}",
            std::mem::size_of_val(&TABLES)
        );
    }
}
