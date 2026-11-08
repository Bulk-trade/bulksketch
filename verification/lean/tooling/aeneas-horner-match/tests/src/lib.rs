pub fn split_then_zip(coefficients: &[u64], points: &[u64], out: &mut [u64]) {
    let Some((&leading, rest)) = coefficients.split_last() else {
        return;
    };
    for (target, &point) in out.iter_mut().zip(points) {
        *target = rest.iter().rev().fold(leading, |value, &coefficient| {
            value ^ point ^ coefficient
        });
    }
}

pub fn zip_without_split(points: &[u64], out: &mut [u64]) {
    for (target, &point) in out.iter_mut().zip(points) {
        *target = point;
    }
}
