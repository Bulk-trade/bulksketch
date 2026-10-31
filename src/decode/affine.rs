//! Least affine multiple and exact affine-coset root recovery.
//!
//! All input-dependent coefficients use the existing row arena. The only fixed
//! local arrays are the binary map's three 64-word columns; immutable Frobenius
//! columns depend on the registered field, never a request.
#![forbid(unsafe_code)]

use crate::{
    backend::contract::BulkKernels,
    field::BinaryField,
    poly::{Dense, Polynomial},
    types::{DecodeFailure, RawProduct},
};

/// Native carryless-product predictor, independent of the selected backend.
/// A full in-row square costs 3d scalar square/reduction instructions plus
/// two vector products for each high input and eight-output block. Gaussian
/// scale-XOR uses two products per eight words; pivot normalization is scalar.
/// The mapped inverse uses eight three-product multiplies and four raw squares.
/// Table lookups, binary-map XORs, loads and shift reductions are not CLMULs;
/// this selector is neither a work bound nor a cycle estimate.
const fn square_products(degree: u64) -> u64 {
    3 * degree + 2 * (degree / 2) * degree.div_ceil(8)
}

const fn predicted_affine(degree: usize) -> bool {
    if degree < 3 || degree >= 64 {
        return false;
    }
    let d = degree as u64;
    let unit_columns = 1 + (usize::BITS - (degree - 1).leading_zeros()) as u64;
    let pivots = d.saturating_sub(unit_columns);
    let mut gaussian = 0;
    let mut column = unit_columns;
    while column <= d {
        let mut pivot = 0;
        while pivot < column {
            gaussian += 2 * ((d - pivot).div_ceil(8) + (column + 1).div_ceil(8));
            pivot += 1;
        }
        column += 1;
    }
    let normalization = 3 * d * (d + 1);
    let inverses = 28 * pivots;
    let map = 16 * d;
    let subspaces = 6 * d * (d - 1);
    gaussian + normalization + inverses + map + subspaces < (64 - d) * square_products(d)
}

// Derive the mask at compile time; row dispatch is one bounded bit test,
// never the Gaussian predictor's nested loops on the decode hot path.
const PREFERRED_MASK: u64 = {
    let mut degree = 3;
    let mut mask = 0;
    while degree < 64 {
        if predicted_affine(degree) {
            mask |= 1_u64 << degree;
        }
        degree += 1;
    }
    mask
};

pub(super) const fn preferred<F: BinaryField>(degree: usize) -> bool {
    degree < F::BITS as usize && degree < 64 && PREFERRED_MASK & (1_u64 << degree) != 0
}

/// Largest degree admitted by the GF64 operation predictor, derived at compile
/// time so request admission never scans degree candidates.
pub(crate) const MAX_PREFERRED_DEGREE: usize = {
    let mut degree = 3;
    let mut maximum = 0;
    while degree < 64 {
        if preferred::<crate::field::Gf64>(degree) {
            maximum = degree;
        }
        degree += 1;
    }
    maximum
};

/// Compare eight-lane Horner products with the split predictor after the
/// actual rank is known. Splitting reserves rank full modular squares, three
/// mapped inverses per root and one raw quadratic-check square per root.
/// As above, this counts CLMUL instructions, not elapsed time or logical work.
pub(super) fn enumerate_preferred(degree: usize, rank: usize) -> bool {
    let Some(points) = 1_u64.checked_shl(rank as u32) else {
        return false;
    };
    let d = degree as u64;
    let Some(enumeration) = points.div_ceil(8).checked_mul(6 * d) else {
        return false;
    };
    enumeration <= rank as u64 * square_products(d) + (3 * 28 + 1) * d
}

/// Return c+sum(a_i X^(2^i)) divisible by the monic input polynomial.
/// `affine`, `residue`, `vector`, and `witness` need d+1,d,d,d+1 words.
/// Rows and witnesses together need 2*d*d+d words.
pub(super) fn multiple<F: BinaryField, K: BulkKernels<F>>(
    polynomial: &[u64],
    table: &[u64],
    factors: &mut [u64],
    affine: &mut [u64],
    work: &mut [u64],
    raw: &mut [RawProduct],
) -> usize {
    let d = polynomial.len() - 1;
    let width = d + 1;
    let (rows, rest) = factors.split_at_mut(d * d);
    let witnesses = &mut rest[..d * width];
    rows.fill(0);
    witnesses.fill(0);
    let (residue, rest) = work.split_at_mut(d);
    let (vector, rest) = rest.split_at_mut(d);
    let witness = &mut rest[..width];
    residue.fill(0);
    residue[0] = 1;
    for column in 0..=d {
        vector.copy_from_slice(residue);
        witness.fill(0);
        witness[column] = 1;
        let mut pivot = None;
        for i in 0..d {
            let scale = vector[i];
            if scale == 0 {
                continue;
            }
            if rows[i * d + i] == 0 {
                pivot = Some(i);
                break;
            }
            K::scale_xor(&mut vector[i..], &rows[i * d + i..(i + 1) * d], scale);
            K::scale_xor(
                &mut witness[..=column],
                &witnesses[i * width..i * width + column + 1],
                scale,
            );
        }
        let Some(pivot) = pivot else {
            affine[..=column].copy_from_slice(&witness[..=column]);
            return column + 1;
        };
        let inverse = if vector[pivot] == 1 {
            1
        } else {
            K::inverse(vector[pivot]).expect("nonzero affine pivot")
        };
        for (dst, &value) in rows[pivot * d + pivot..(pivot + 1) * d]
            .iter_mut()
            .zip(&vector[pivot..])
        {
            *dst = K::mul(value, inverse);
        }
        for (dst, &value) in witnesses[pivot * width..pivot * width + column + 1]
            .iter_mut()
            .zip(&witness[..=column])
        {
            *dst = K::mul(value, inverse);
        }
        if column == 0 {
            residue.fill(0);
            residue[1] = 1;
        } else if column != d {
            <Dense as Polynomial<F, K>>::square_mod_into(residue, polynomial, table, vector, raw);
            residue.copy_from_slice(vector);
        }
    }
    unreachable!("d+1 vectors in dimension d are dependent")
}

/// Column elimination preserves a preimage witness for every image pivot.
/// Every dependent column gives one independent kernel direction. The returned
/// base plus that kernel is exactly the complete solution set of L(X)=c.
pub(super) fn solve_map<F: BinaryField, K: BulkKernels<F>>(
    affine: &[u64],
    kernel: &mut [u64; 64],
) -> Option<(u64, usize)> {
    let bits = F::BITS as usize;
    let mut columns = [0; 64];
    for (power, &coefficient) in affine[1..].iter().enumerate() {
        if coefficient == 0 {
            continue;
        }
        if F::BITS == 64 {
            let row = &FROBENIUS_COLUMNS[power];
            if coefficient == 1 {
                for (dst, &value) in columns.iter_mut().zip(row) {
                    *dst ^= value;
                }
            } else {
                K::scale_xor(&mut columns, row, coefficient);
            }
        } else {
            for (bit, dst) in columns[..bits].iter_mut().enumerate() {
                *dst ^= K::mul(coefficient, K::frobenius(1_u64 << bit, power as u32));
            }
        }
    }
    let mut images = [0; 64];
    let mut preimages = [0; 64];
    let mut rank = 0;
    for (bit, &column) in columns[..bits].iter().enumerate() {
        let mut original = 1_u64 << bit;
        let mut image = column;
        while image != 0 {
            let pivot = image.trailing_zeros() as usize;
            if images[pivot] == 0 {
                images[pivot] = image;
                preimages[pivot] = original;
                break;
            }
            image ^= images[pivot];
            original ^= preimages[pivot];
        }
        if image == 0 {
            kernel[rank] = original;
            rank += 1;
        }
    }
    let mut target = affine[0];
    let mut solution = 0;
    while target != 0 {
        let pivot = target.trailing_zeros() as usize;
        if images[pivot] == 0 {
            return None;
        }
        target ^= images[pivot];
        solution ^= preimages[pivot];
    }
    Some((solution, rank))
}

fn linear_eval<F: BinaryField, K: BulkKernels<F>>(linear: &[u64], mut x: u64) -> u64 {
    let mut out = 0;
    for (i, &coefficient) in linear.iter().enumerate() {
        out ^= K::mul(coefficient, x);
        if i + 1 != linear.len() {
            x = K::square(x);
        }
    }
    out
}

pub(super) fn subspace_start(rank: usize) -> usize {
    rank * (rank + 1) / 2
}

/// Prefix annihilators A_0=X, A_(j+1)=A_j^2+A_j(b_j)*A_j.
/// The triangular table takes (rank+1)(rank+2)/2 words.
pub(super) fn subspaces<F: BinaryField, K: BulkKernels<F>>(basis: &[u64], table: &mut [u64]) {
    table[0] = 1;
    for (rank, &direction) in basis.iter().enumerate() {
        let start = subspace_start(rank);
        let next = subspace_start(rank + 1);
        let (previous, rest) = table.split_at_mut(next);
        let previous = &previous[start..next];
        let output = &mut rest[..rank + 2];
        let at_direction = linear_eval::<F, K>(previous, direction);
        output.fill(0);
        for (i, &coefficient) in previous.iter().enumerate() {
            output[i] ^= K::mul(at_direction, coefficient);
            output[i + 1] ^= K::square(coefficient);
        }
    }
}

/// A_(rank-1)(X)+A_(rank-1)(base) modulo the current monic factor.
/// Its zero set partitions the current coset into exactly the two child cosets.
pub(super) fn splitter<F: BinaryField, K: BulkKernels<F>>(
    polynomial: &[u64],
    table: &[u64],
    linear: &[u64],
    base: u64,
    output: &mut [u64],
    work: &mut [u64],
    raw: &mut [RawProduct],
) -> usize {
    let d = polynomial.len() - 1;
    output[..d].fill(0);
    output[0] = linear_eval::<F, K>(linear, base);
    let (residue, rest) = work.split_at_mut(d);
    let squared = &mut rest[..d];
    residue.fill(0);
    residue[1] = 1;
    for (i, &coefficient) in linear.iter().enumerate() {
        K::scale_xor(&mut output[..d], residue, coefficient);
        if i + 1 != linear.len() {
            <Dense as Polynomial<F, K>>::square_mod_into(residue, polynomial, table, squared, raw);
            residue.copy_from_slice(squared);
        }
    }
    output[..d]
        .iter()
        .rposition(|&x| x != 0)
        .map_or(0, |i| i + 1)
}

/// Enumerate the exact solution coset in Gray order and test the original
/// residual polynomial. Distinct d roots of a monic degree-d polynomial prove
/// complete splitting, so no extra polynomial reconstruction is necessary.
pub(super) fn enumerate<F: BinaryField, K: BulkKernels<F>>(
    polynomial: &[u64],
    base: u64,
    basis: &[u64],
    roots: &mut [u64],
    work: &mut [u64],
) -> Result<usize, DecodeFailure> {
    let d = polynomial.len() - 1;
    let (points, values) = work.split_at_mut(work.len() / 2);
    let batch = points.len().min(values.len());
    // Keep all interior batches complete native vectors. Otherwise each arena-
    // sized batch repeats a padded tail outside the selector's product count.
    let batch = if batch >= 8 { batch / 8 * 8 } else { batch };
    let count = 1_usize
        .checked_shl(basis.len() as u32)
        .expect("charged enumeration rank");
    let mut x = base;
    let mut found = 0;
    for start in (0..count).step_by(batch) {
        let len = batch.min(count - start);
        for (offset, point) in points[..len].iter_mut().enumerate() {
            let index = start + offset;
            if index != 0 {
                x ^= basis[index.trailing_zeros() as usize];
            }
            *point = x;
        }
        K::horner_many(polynomial, &points[..len], &mut values[..len]);
        for (&point, &value) in points[..len].iter().zip(&values[..len]) {
            if value == 0 {
                if point == 0 {
                    return Err(DecodeFailure::InvalidLocator);
                }
                if found == d {
                    return Err(DecodeFailure::NotSplit);
                }
                roots[found] = point;
                found += 1;
            }
        }
    }
    if found != d {
        return Err(DecodeFailure::NotSplit);
    }
    Ok(found)
}

// All GF64 basis images are immutable field data, built at compile time. This
// avoids input-dependent map caches and their uncharged first-use work.
static FROBENIUS_COLUMNS: [[u64; 64]; 64] = frobenius_columns();

const fn frobenius_columns() -> [[u64; 64]; 64] {
    let mut rows = [[0; 64]; 64];
    let mut bit = 0;
    while bit < 64 {
        rows[0][bit] = 1_u64 << bit;
        bit += 1;
    }
    let mut power = 1;
    while power < 64 {
        bit = 0;
        while bit < 64 {
            rows[power][bit] = square_column(rows[power - 1][bit]);
            bit += 1;
        }
        power += 1;
    }
    rows
}

const fn square_column(word: u64) -> u64 {
    let mut result = 0_u128;
    let mut bit = 0;
    while bit < 64 {
        result ^= (((word >> bit) & 1) as u128) << (2 * bit);
        bit += 1;
    }
    let polynomial = (1_u128 << 64) | 0x1b;
    bit = 128;
    while bit > 64 {
        bit -= 1;
        if result & (1_u128 << bit) != 0 {
            result ^= polynomial << (bit - 64);
        }
    }
    result as u64
}
