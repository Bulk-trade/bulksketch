#![forbid(unsafe_code)]

fn normalized_len(coefficients: &[u64]) -> usize {
    coefficients.iter().rposition(|&word| word != 0).map_or(0, |i| i + 1)
}

pub fn prefix_zip_read(dst: &mut [u64], src: &[u64]) -> usize {
    let size = src.len();
    assert!(size <= dst.len());
    for (target, &source) in dst[..size].iter_mut().zip(src) {
        *target = source;
    }
    normalized_len(&dst[..size])
}

pub fn prefix_stride_read(dst: &mut [u64], src: &[u64]) -> usize {
    let size = 2 * src.len();
    assert!(size <= dst.len());
    for (target, &source) in dst[..size].iter_mut().step_by(2).zip(src) {
        *target = source;
    }
    normalized_len(&dst[..size])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prefix_read_uses_updated_values_and_preserves_the_tail() {
        let mut zipped = [0, 7, 8, 41];
        assert_eq!(prefix_zip_read(&mut zipped, &[9, 0, 0]), 1);
        assert_eq!(zipped, [9, 0, 0, 41]);

        let mut stride = [0, 0, 7, 0, 8, 0, 41];
        assert_eq!(prefix_stride_read(&mut stride, &[9, 0, 0]), 1);
        assert_eq!(stride, [9, 0, 0, 0, 0, 0, 41]);

        stride[5] = 33;
        assert_eq!(prefix_stride_read(&mut stride, &[0, 0, 0]), 6);
        assert_eq!(stride, [0, 0, 0, 0, 0, 33, 41]);
    }
}
