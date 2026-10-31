//! Allocation-free ascending polynomials over the selected field kernels.
#![forbid(unsafe_code)]

use super::{BinaryField, BulkKernels, Dense, Polynomial, RawProduct};

impl<F: BinaryField, K: BulkKernels<F>> Polynomial<F, K> for Dense {
    fn mul_into(a: &[u64], b: &[u64], dst: &mut [u64], raw: &mut [RawProduct]) -> usize {
        if a.is_empty() || b.is_empty() {
            return 0;
        }
        let size = a.len() + b.len();
        assert!(dst.len() >= size && raw.len() >= size);
        let len = size - 1;
        raw[..len].fill(RawProduct::default());
        // Reduction is XOR-linear; each coefficient needs only one reduction,
        // regardless of how many raw products contribute to it.
        for (i, &left) in a.iter().enumerate() {
            for (slot, &right) in raw[i..i + b.len()].iter_mut().zip(b) {
                let product = K::raw_mul(left, right);
                slot.lo ^= product.lo;
                slot.hi ^= product.hi;
            }
        }
        for (target, &product) in dst[..len].iter_mut().zip(&raw[..len]) {
            *target = K::reduce(product);
        }
        normalized_len(&dst[..len])
    }

    fn square_into(a: &[u64], dst: &mut [u64], raw: &mut [RawProduct]) -> usize {
        let size = 2 * a.len();
        assert!(dst.len() >= size && raw.len() >= size);
        dst[..size].fill(0);
        for (target, &coefficient) in dst[..size].iter_mut().step_by(2).zip(a) {
            *target = K::square(coefficient);
        }
        normalized_len(&dst[..size])
    }

    fn div_rem_into(
        a: &[u64],
        b: &[u64],
        q: &mut [u64],
        rem: &mut [u64],
        raw: &mut [RawProduct],
    ) -> (usize, usize) {
        let &leading = b.last().expect("zero polynomial divisor");
        let inverse = if leading == 1 {
            1
        } else {
            K::inverse(leading).expect("noncanonical polynomial divisor")
        };
        let size = a.len() + 1;
        assert!(q.len() >= size && rem.len() >= size && raw.len() >= size);
        q[..size].fill(0);
        rem[..size].fill(0);
        for (target, &coefficient) in raw[..a.len()].iter_mut().zip(a) {
            *target = RawProduct {
                lo: coefficient,
                hi: 0,
            };
        }
        let degree = b.len() - 1;
        // Lower slots retain raw XOR sums. Only a reduced leading slot may
        // enter field multiplication; eliminated slots are never read again.
        for top in (degree..a.len()).rev() {
            let mut factor = K::reduce(raw[top]);
            if inverse != 1 {
                factor = K::mul(factor, inverse);
            }
            let offset = top - degree;
            q[offset] = factor;
            if factor == 0 {
                continue;
            }
            if factor == 1 {
                for (slot, &coefficient) in raw[offset..top].iter_mut().zip(&b[..degree]) {
                    slot.lo ^= coefficient;
                }
                continue;
            }
            for (slot, &coefficient) in raw[offset..top].iter_mut().zip(&b[..degree]) {
                let product = K::raw_mul(factor, coefficient);
                slot.lo ^= product.lo;
                slot.hi ^= product.hi;
            }
        }
        let remainder_size = degree.min(a.len());
        for (target, &product) in rem[..remainder_size].iter_mut().zip(raw.iter()) {
            *target = K::reduce(product);
        }
        (
            normalized_len(&q[..size]),
            normalized_len(&rem[..remainder_size]),
        )
    }

    fn exact_divide_into(
        a: &[u64],
        b: &[u64],
        q: &mut [u64],
        rem: &mut [u64],
        raw: &mut [RawProduct],
    ) -> Option<usize> {
        let (q_len, rem_len) = <Self as Polynomial<F, K>>::div_rem_into(a, b, q, rem, raw);
        if rem_len != 0 {
            q[..=a.len()].fill(0);
            return None;
        }
        Some(q_len)
    }

    fn monic_gcd_into(
        a: &[u64],
        b: &[u64],
        dst: &mut [u64],
        work: &mut [u64],
        raw: &mut [RawProduct],
    ) -> usize {
        let max_len = a.len().max(b.len());
        let width = max_len + 1;
        assert!(dst.len() >= max_len && work.len() >= 4 * width && raw.len() >= 2 * width);
        let (mut left, rest) = work[..4 * width].split_at_mut(width);
        let (mut right, rest) = rest.split_at_mut(width);
        let (quotient, mut remainder) = rest.split_at_mut(width);
        left[..a.len()].copy_from_slice(a);
        right[..b.len()].copy_from_slice(b);
        let (mut left_len, mut right_len) = (a.len(), b.len());
        while right_len != 0 {
            let (_, len) = <Self as Polynomial<F, K>>::div_rem_into(
                &left[..left_len],
                &right[..right_len],
                quotient,
                remainder,
                raw,
            );
            std::mem::swap(&mut left, &mut right);
            std::mem::swap(&mut right, &mut remainder);
            left_len = right_len;
            right_len = len;
        }
        dst[..max_len].fill(0);
        if left_len != 0 {
            if left[left_len - 1] == 1 {
                dst[..left_len].copy_from_slice(&left[..left_len]);
            } else {
                let inverse =
                    K::inverse(left[left_len - 1]).expect("nonzero gcd leading coefficient");
                K::scale_xor(&mut dst[..left_len], &left[..left_len], inverse);
            }
        }
        left_len
    }

    fn eval_many_into(coefficients: &[u64], points: &[u64], out: &mut [u64]) {
        K::horner_many(coefficients, points, out);
    }

    fn xor_coefficient(dst: &mut [u64], len: usize, index: usize, value: u64) -> usize {
        assert!(len <= dst.len() && index < dst.len());
        let size = len.max(index + 1);
        dst[len..size].fill(0);
        dst[index] ^= value;
        normalized_len(&dst[..size])
    }

    fn prepare_square_table(modulus: &[u64], table: &mut [u64], work: &mut [u64]) {
        assert!(modulus.len() >= 4 && modulus.last() == Some(&1));
        let degree = modulus.len() - 1;
        let rows = degree / 2;
        assert!(table.len() >= degree * rows && work.len() >= 4 * (degree + 1));
        let current = &mut work[..degree];
        current.copy_from_slice(&modulus[..degree]);
        // X^d = f's low coefficients modulo monic f. The first stored
        // exponent is d for even d, d+1 for odd d; successive rows add two.
        if !degree.is_multiple_of(2) {
            times_x_mod::<F, K>(current, modulus);
        }
        for row in 0..rows {
            table[row * degree..(row + 1) * degree].copy_from_slice(current);
            if row + 1 != rows {
                times_x_mod::<F, K>(current, modulus);
                times_x_mod::<F, K>(current, modulus);
            }
        }
    }

    fn square_mod_into(
        a: &[u64],
        modulus: &[u64],
        table: &[u64],
        dst: &mut [u64],
        raw: &mut [RawProduct],
    ) -> usize {
        assert!(modulus.len() >= 4 && modulus.last() == Some(&1));
        let degree = modulus.len() - 1;
        assert!(a.len() <= degree && dst.len() >= degree && raw.len() > 2 * degree);
        assert_eq!(table.len(), degree * (degree / 2));
        if K::square_mod(a, table, &mut dst[..degree], raw) {
            return normalized_len(&dst[..degree]);
        }
        let accumulators = &mut raw[..degree];
        accumulators.fill(RawProduct::default());
        let first_high = degree.div_ceil(2);
        // The table is linear only after squaring each coefficient: Frobenius
        // acts on coefficients as well as exponents in the extension field.
        for (i, &coefficient) in a.iter().enumerate() {
            let square = K::square(coefficient);
            if i < first_high {
                accumulators[2 * i].lo ^= square;
            } else {
                let start = (i - first_high) * degree;
                for (slot, &entry) in accumulators.iter_mut().zip(&table[start..start + degree]) {
                    let product = K::raw_mul(square, entry);
                    slot.lo ^= product.lo;
                    slot.hi ^= product.hi;
                }
            }
        }
        for (target, &product) in dst[..degree].iter_mut().zip(accumulators.iter()) {
            *target = K::reduce(product);
        }
        normalized_len(&dst[..degree])
    }
}

fn normalized_len(coefficients: &[u64]) -> usize {
    coefficients
        .iter()
        .rposition(|&coefficient| coefficient != 0)
        .map_or(0, |i| i + 1)
}

fn times_x_mod<F: BinaryField, K: BulkKernels<F>>(coefficients: &mut [u64], modulus: &[u64]) {
    let len = coefficients.len();
    let leading = coefficients[len - 1];
    coefficients.copy_within(..len - 1, 1);
    coefficients[0] = 0;
    K::scale_xor(coefficients, &modulus[..len], leading);
}
