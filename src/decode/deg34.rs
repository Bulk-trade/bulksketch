//! Cleared Newton guards and closed-form GF64 factor solvers for degree 3 and 4.
//! Callers charge before entry and certify returned roots before using them.
#![forbid(unsafe_code)]

use crate::{backend::contract::BulkKernels, field::BinaryField};

const OMEGA: u64 = 0x19c9_369f_278a_dc02;

/// Six words: five ascending cleared coefficients, then the denominator.
pub(super) fn guard<F: BinaryField, K: BulkKernels<F>>(
    odd: &[u64],
    degree: usize,
    out: &mut [u64],
) -> bool {
    let s = odd[0];
    let s2 = K::square(s);
    let s4 = K::square(s2);
    let a = odd[1] ^ K::mul(s, s2);
    let b = odd[2] ^ K::mul(odd[1], s2);
    let denominator;
    if degree == 3 {
        denominator = a;
        if denominator == 0 {
            return false;
        }
        out[..5].copy_from_slice(&[K::square(a) ^ K::mul(s, b), b, K::mul(s, a), a, 0]);
    } else {
        let d = odd[2] ^ K::mul(s, s4);
        let c = odd[3] ^ K::mul(s, K::square(odd[1])) ^ K::mul(a, s4);
        denominator = K::mul(a, odd[1]) ^ K::mul(s, d);
        if denominator == 0 {
            return false;
        }
        let u2 = K::mul(b, odd[1]) ^ K::mul(s, c);
        out[..5].copy_from_slice(&[
            K::mul(a, c) ^ K::mul(b, d),
            K::mul(a, denominator) ^ K::mul(s, u2),
            u2,
            K::mul(s, denominator),
            denominator,
        ]);
    }
    out[5] = denominator;
    for index in degree..odd.len().min(degree + 2) {
        let exponent = 2 * index + 1;
        #[cfg(test)]
        crate::types::small_degree_observer::residual(exponent);
        let mut residual = K::mul(denominator, odd[index]);
        for lag in 1..=degree {
            let power = exponent - lag;
            let squares = power.trailing_zeros();
            let mut observed = odd[(power >> squares) / 2];
            for _ in 0..squares {
                observed = K::square(observed);
            }
            residual ^= K::mul(out[degree - lag], observed);
        }
        if residual != 0 {
            return false;
        }
    }
    true
}

pub(super) fn normalize<F: BinaryField, K: BulkKernels<F>>(
    cleared: &[u64],
    s: u64,
    degree: usize,
    factor: &mut [u64],
) {
    let inverse = K::inverse(cleared[5]).expect("passed nonsingular Newton guard");
    for index in 0..degree - 1 {
        factor[index] = K::mul(cleared[index], inverse);
    }
    factor[degree - 1] = s;
    factor[degree] = 1;
}

fn quadratic<F: BinaryField, K: BulkKernels<F>>(target: u64) -> Option<u64> {
    let root = K::solve_quadratic(target)?;
    (K::square(root) ^ root == target).then_some(root)
}

fn cube_root<F: BinaryField, K: BulkKernels<F>>(t: u64) -> Option<u64> {
    let t16 = K::frobenius(t, 4);
    let t49 = K::mul(K::mul(K::square(t16), t16), t);
    let mut u = t;
    for _ in 0..10 {
        u = K::mul(K::frobenius(u, 6), t49);
    }
    u = K::mul(u, t);
    (u != 0 && K::mul(K::square(u), u) == t).then_some(u)
}

fn cubic<F: BinaryField, K: BulkKernels<F>>(a: u64, b: u64, c: u64) -> Option<[u64; 3]> {
    let p = K::square(a) ^ b;
    let q = K::mul(a, b) ^ c;
    if q == 0 {
        return None;
    }
    let inverse = K::inverse(q)?;
    let z = quadratic::<F, K>(K::mul(K::mul(K::square(p), p), K::square(inverse)))?;
    let t = K::mul(q, z);
    let u = cube_root::<F, K>(if t == 0 { q } else { t })?;
    let v = if p == 0 { 0 } else { K::mul(p, K::inverse(u)?) };
    let ou = K::mul(OMEGA, u);
    let ov = K::mul(OMEGA, v);
    Some([a ^ u ^ v, a ^ ou ^ ov ^ v, a ^ ou ^ u ^ ov])
}

/// The single complete product certificate, also used privately for a quartic's kernel.
pub(super) fn certificate<F: BinaryField, K: BulkKernels<F>>(
    factor: &[u64],
    roots: &[u64],
    product: &mut [u64],
) -> bool {
    if roots.len() + 1 != factor.len()
        || roots
            .iter()
            .enumerate()
            .any(|(i, &x)| x == 0 || x & !F::MASK != 0 || roots[..i].contains(&x))
    {
        return false;
    }
    let product = &mut product[..factor.len()];
    product.fill(0);
    product[0] = 1;
    for (degree, &root) in roots.iter().enumerate() {
        product[degree + 1] = product[degree];
        for j in (1..=degree).rev() {
            product[j] = product[j - 1] ^ K::mul(root, product[j]);
        }
        product[0] = K::mul(root, product[0]);
    }
    product == factor
}

fn affine_quartic<F: BinaryField, K: BulkKernels<F>>(b: u64, c: u64, d: u64) -> Option<[u64; 4]> {
    if c == 0 {
        return None;
    }
    let kernel = cubic::<F, K>(0, b, c)?;
    if !certificate::<F, K>(&[c, b, 0, 1], &kernel, &mut [0; 4]) {
        return None;
    }
    let u = *kernel.iter().min().expect("three kernel roots");
    #[cfg(test)]
    crate::types::small_degree_observer::selected(u);
    let v = b ^ K::square(u);
    if u == 0 || v == 0 || K::mul(u, v) != c {
        return None;
    }
    let inverse = K::inverse(c)?;
    let iu2 = K::square(K::mul(v, inverse));
    let iv2 = K::square(K::mul(u, inverse));
    let w = K::mul(v, quadratic::<F, K>(K::mul(d, iv2))?);
    let x = K::mul(u, quadratic::<F, K>(K::mul(w, iu2))?);
    let y = K::mul(u, quadratic::<F, K>(K::mul(w ^ v, iu2))?);
    Some([x, x ^ u, y, y ^ u])
}

fn quartic<F: BinaryField, K: BulkKernels<F>>(factor: &[u64]) -> Option<[u64; 4]> {
    let (a, b, c, d) = (factor[3], factor[2], factor[1], factor[0]);
    if a == 0 {
        return affine_quartic::<F, K>(b, c, d);
    }
    let ratio = K::mul(c, K::inverse(a)?);
    // F63 = square(F31(F31(x))); reuse the existing fixed maps.
    let shift = K::square(K::frobenius(K::frobenius(ratio, 31), 31));
    let e2 = K::square(shift);
    let denominator = K::square(e2) ^ K::mul(b, e2) ^ d;
    if denominator == 0 {
        return None;
    }
    let inverse = K::inverse(denominator)?;
    let mut roots = affine_quartic::<F, K>(
        K::mul(b ^ K::mul(a, shift), inverse),
        K::mul(a, inverse),
        inverse,
    )?;
    if roots.contains(&0) {
        return None;
    }
    let mut prefixes = [1; 4];
    for i in 1..4 {
        prefixes[i] = K::mul(prefixes[i - 1], roots[i - 1]);
    }
    let mut inverse = K::inverse(K::mul(prefixes[3], roots[3]))?;
    for i in (0..4).rev() {
        let original = roots[i];
        roots[i] = K::mul(prefixes[i], inverse) ^ shift;
        inverse = K::mul(inverse, original);
    }
    Some(roots)
}

/// Returned candidates are deliberately uncertified. A miss writes no output.
pub(super) fn solve<F: BinaryField, K: BulkKernels<F>>(
    factor: &[u64],
    output: &mut [u64],
) -> Option<usize> {
    debug_assert_eq!(F::BITS, 64);
    let degree = factor.len() - 1;
    let roots = if degree == 3 {
        let roots = cubic::<F, K>(factor[2], factor[1], factor[0])?;
        [roots[0], roots[1], roots[2], 0]
    } else {
        quartic::<F, K>(factor)?
    };
    output[..degree].copy_from_slice(&roots[..degree]);
    #[cfg(test)]
    return crate::types::small_degree_observer::returned(output, degree);
    #[cfg(not(test))]
    Some(degree)
}

#[cfg(test)]
mod tests;
