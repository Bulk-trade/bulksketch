//! Independent algebraic checks for the backend operations used by DirectTwo.
#![forbid(unsafe_code)]

use crate::{
    backend::{contract::Arithmetic, portable::Portable},
    field::{Gf64, reference},
};

macro_rules! checked_backends {
    ($check:ident, $($argument:expr),+ $(,)?) => {{
        $check::<Portable>("portable", $($argument),+);
        #[cfg(target_arch = "x86_64")]
        {
            if std::is_x86_feature_detected!("pclmulqdq") {
                $check::<crate::backend::x86_pclmul::Pclmul>("pclmul", $($argument),+);
                if crate::backend::x86_vpclmul512::available() {
                    $check::<crate::backend::x86_vpclmul512::Vpclmul512>(
                        "vpclmul512", $($argument),+
                    );
                }
            }
        }
    }};
}

fn next(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let mut value = *state;
    value = (value ^ (value >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    value = (value ^ (value >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    value ^ (value >> 31)
}

fn input_corpus() -> Vec<u64> {
    let mut inputs = vec![
        0,
        1,
        u64::MAX,
        u64::MAX >> 1,
        0xaaaa_aaaa_aaaa_aaaa,
        0x5555_5555_5555_5555,
    ];
    inputs.extend((0..64).map(|bit| 1_u64 << bit));
    inputs.extend((0..64).map(|bit| !(1_u64 << bit)));
    // Powers of the polynomial-basis element Z, independently multiplied.
    // This does not assume that Z generates the entire multiplicative group.
    let mut power = 1;
    for _ in 0..2048 {
        inputs.push(power);
        power = reference::mul::<Gf64>(power, 2);
    }
    let mut seed = 0x782d_6d61_7073_0001;
    inputs.extend((0..2048).map(|_| next(&mut seed)));
    inputs.sort_unstable();
    inputs.dedup();
    inputs
}

/// Ordinary binary exponentiation, deliberately independent of addition chains
/// and every production square, Frobenius map, multiplication and reduction.
fn bit_serial_inverse(input: u64) -> Option<u64> {
    if input == 0 {
        return None;
    }
    let mut exponent = u64::MAX - 1;
    let mut base = input;
    let mut result = 1;
    while exponent != 0 {
        if exponent & 1 != 0 {
            result = reference::mul::<Gf64>(result, base);
        }
        exponent >>= 1;
        if exponent != 0 {
            base = reference::mul::<Gf64>(base, base);
        }
    }
    Some(result)
}

fn check_inverses<B: Arithmetic<Gf64>>(backend: &str, cases: &[(u64, Option<u64>)]) {
    for &(input, expected) in cases {
        let actual = B::inverse(input);
        assert_eq!(
            actual, expected,
            "inverse backend={backend} input={input:#018x}"
        );
        if let Some(inverse) = actual {
            assert_eq!(
                reference::mul::<Gf64>(input, inverse),
                1,
                "inverse product backend={backend} input={input:#018x}"
            );
        }
    }
    eprintln!("inverse backend={backend} inputs={}", cases.len());
}

#[test]
fn inverse_matches_bit_serial_exponentiation() {
    // Production mode: GF64 inverse used by the charged tiny DirectTwo path.
    let cases: Vec<_> = input_corpus()
        .into_iter()
        .map(|input| (input, bit_serial_inverse(input)))
        .collect();
    checked_backends!(check_inverses, &cases);
}

/// Column elimination using highest output bits as pivots. Production constants
/// use lowest-row Gauss-Jordan elimination; this oracle builds its own Q images
/// with bit-serial arithmetic and never reads the production constants.
struct QuadraticOracle {
    images: [u64; 64],
    preimages: [u64; 64],
}

impl QuadraticOracle {
    fn new() -> Self {
        let mut oracle = Self {
            images: [0; 64],
            preimages: [0; 64],
        };
        let mut rank = 0;
        // The kernel of Q is {0, 1}; omitting input bit zero fixes the root.
        for bit in 1..64 {
            let mut preimage = 1_u64 << bit;
            let mut image = reference::mul::<Gf64>(preimage, preimage) ^ preimage;
            while image != 0 {
                let pivot = usize::try_from(63 - image.leading_zeros()).unwrap();
                if oracle.images[pivot] == 0 {
                    oracle.images[pivot] = image;
                    oracle.preimages[pivot] = preimage;
                    rank += 1;
                    break;
                }
                image ^= oracle.images[pivot];
                preimage ^= oracle.preimages[pivot];
            }
        }
        assert_eq!(rank, 63, "independent GF64 quadratic oracle rank");
        oracle
    }

    fn solve(&self, mut image: u64) -> Option<u64> {
        let mut root = 0;
        while image != 0 {
            let pivot = usize::try_from(63 - image.leading_zeros()).unwrap();
            if self.images[pivot] == 0 {
                return None;
            }
            image ^= self.images[pivot];
            root ^= self.preimages[pivot];
        }
        Some(root)
    }
}

fn bit_serial_trace(input: u64) -> u8 {
    let mut trace = 0;
    let mut conjugate = input;
    for _ in 0..64 {
        trace ^= conjugate;
        conjugate = reference::mul::<Gf64>(conjugate, conjugate);
    }
    u8::try_from(trace).expect("independent absolute trace is a bit")
}

fn check_quadratics<B: Arithmetic<Gf64>>(backend: &str, cases: &[(u64, u8, Option<u64>)]) {
    let mut solvable = 0;
    let mut no_solution = 0;
    for &(input, trace, expected) in cases {
        assert_eq!(
            B::trace(input),
            trace,
            "trace backend={backend} input={input:#018x}"
        );
        let actual = B::solve_quadratic(input);
        assert_eq!(
            actual, expected,
            "quadratic backend={backend} input={input:#018x} trace={trace}"
        );
        if let Some(root) = actual {
            solvable += 1;
            assert_eq!(
                root & 1,
                0,
                "canonical quadratic root backend={backend} input={input:#018x}"
            );
            assert_eq!(
                reference::mul::<Gf64>(root, root) ^ root,
                input,
                "quadratic equation backend={backend} input={input:#018x}"
            );
        } else {
            no_solution += 1;
        }
    }
    eprintln!(
        "quadratic backend={backend} inputs={} solvable={solvable} no_solution={no_solution}",
        cases.len()
    );
}

#[test]
fn quadratic_matches_bit_serial_elimination() {
    // Production mode: canonical GF64 quadratic solving inside tiny DirectTwo,
    // including unsolvable inputs that must be rejected before reconstruction.
    let oracle = QuadraticOracle::new();
    let inputs = input_corpus();
    let trace_one = (0..64)
        .map(|bit| 1_u64 << bit)
        .find(|&input| bit_serial_trace(input) == 1)
        .expect("GF64 has a trace-one element");
    let mut cases = Vec::with_capacity(3 * inputs.len());
    for input in inputs {
        let trace = bit_serial_trace(input);
        let expected = oracle.solve(input);
        assert_eq!(expected.is_some(), trace == 0, "oracle solvability");
        cases.push((input, trace, expected));

        // Generate both members of a trace-zero/trace-one pair independently of
        // the solver under test; every canonical root is known before solving.
        let image = reference::mul::<Gf64>(input, input) ^ input;
        assert_eq!(oracle.solve(image), Some(input & !1));
        assert_eq!(oracle.solve(image ^ trace_one), None);
        cases.push((image, 0, Some(input & !1)));
        cases.push((image ^ trace_one, 1, None));
    }
    checked_backends!(check_quadratics, &cases);
}

fn apply_basis(basis: &[u64; 64], mut input: u64) -> u64 {
    let mut output = 0;
    while input != 0 {
        let bit = usize::try_from(input.trailing_zeros()).unwrap();
        output ^= basis[bit];
        input &= input - 1;
    }
    output
}

fn check_map_bytes<B: Arithmetic<Gf64>>(
    backend: &str,
    powers: &[u32],
    bases: &[[u64; 64]; 64],
    oracle: &QuadraticOracle,
) {
    let mut inputs = 0;
    let mut frobenius_checks = 0;
    for byte in 0..8 {
        for value in 0_u64..=255 {
            let input = value << (byte * 8);
            inputs += 1;
            assert_eq!(
                B::solve_quadratic(input),
                oracle.solve(input),
                "quadratic byte backend={backend} byte={byte} value={value:#04x}"
            );
            for &power in powers {
                let basis = &bases[usize::try_from(power % 64).unwrap()];
                assert_eq!(
                    B::frobenius(input, power),
                    apply_basis(basis, input),
                    "Frobenius byte backend={backend} byte={byte} value={value:#04x} power={power}"
                );
                frobenius_checks += 1;
            }
        }
    }
    eprintln!(
        "map_bytes backend={backend} inputs={inputs} quadratic_checks={inputs} \
         frobenius_checks={frobenius_checks}"
    );
}

#[test]
fn linear_maps_exhaustive_byte_positions() {
    // Production mode: GF64 linear maps feeding the tiny DirectTwo inverse and
    // quadratic solve. Every byte value in every position exercises all entries
    // of a byte- or nibble-indexed map, including the trace-one rejection cases.
    let mut bases = [[0; 64]; 64];
    for bit in 0..64 {
        let mut image = 1_u64 << bit;
        for basis in &mut bases {
            basis[bit] = image;
            image = reference::mul::<Gf64>(image, image);
        }
    }
    let powers = [
        0,
        1,
        2,
        3,
        6,
        7,
        12,
        14,
        15,
        21,
        30,
        31,
        42,
        63,
        64,
        u32::MAX,
    ];
    let mut direct_map_checks = 0;
    for byte in 0..8 {
        for value in 0_u64..=255 {
            let input = value << (byte * 8);
            assert_eq!(
                crate::field::frobenius::inverse21(input),
                apply_basis(&bases[21], input),
                "direct inverse Frobenius21 byte={byte} value={value:#04x}"
            );
            direct_map_checks += 1;
        }
    }
    eprintln!("direct_inverse21 checks={direct_map_checks}");
    checked_backends!(check_map_bytes, &powers, &bases, &QuadraticOracle::new());
}
