#![forbid(unsafe_code)]

use {
    super::{
        BackendId, BackendRequest, DecodeExecution, Decoder, InsertDispatch, Pclmul, RowBudget,
        Toggle, detect, toggle,
    },
    crate::field::Gf64,
};

#[test]
fn dispatch_uses_scalar_backend() {
    let _vector_unavailable = detect::vector_fixture(false, false);
    if !std::is_x86_feature_detected!("pclmulqdq") {
        return;
    }
    for request in [
        BackendRequest::Auto,
        BackendRequest::Force(BackendId::Pclmul),
    ] {
        let decoder = Decoder::<Gf64>::new(request, 1).unwrap();
        assert!(
            matches!(
                decoder.begin(RowBudget {
                    nonzero: 1,
                    total: 1
                }),
                DecodeExecution::Pclmul(_)
            ),
            "checked request selects scalar execution"
        );
    }
    let insertion = InsertDispatch::<Gf64>::new(detect::resolve(BackendRequest::Auto).unwrap());
    assert!(
        std::ptr::fn_addr_eq(insertion.toggle, toggle::<Gf64, Pclmul> as Toggle<Gf64>),
        "automatic insertion selects scalar kernels"
    );
    let portable = Decoder::<Gf64>::new(BackendRequest::Force(BackendId::Portable), 1).unwrap();
    assert!(matches!(
        portable.begin(RowBudget {
            nonzero: 1,
            total: 1
        }),
        DecodeExecution::Portable(_)
    ));
}

#[test]
fn unavailable_backend_rejected_at_construction() {
    use {
        crate::{
            BackendError, BackendId, BackendRequest, Decoder, MutableSketch, ShapeLimits,
            SketchShape, types::CreateError,
        },
        std::sync::Arc,
    };
    let _vector_unavailable = detect::vector_fixture(false, false);
    let request = BackendRequest::Force(BackendId::Pclmul);
    let shape = Arc::new(
        SketchShape::<Gf64>::new(
            &[18],
            &ShapeLimits {
                max_wire_bytes: 100_000,
                max_buckets: 16,
                max_capacity_per_bucket: 89,
                max_total_syndrome_words: 1424,
            },
        )
        .unwrap(),
    );
    let frozen = MutableSketch::new(
        Arc::clone(&shape),
        BackendRequest::Force(BackendId::Portable),
    )
    .unwrap()
    .freeze();
    super::detect::without_pclmul(|| {
        assert_eq!(
            Decoder::<Gf64>::new(request, 1).map(|_| ()),
            Err(BackendError(BackendId::Pclmul))
        );
        assert_eq!(
            MutableSketch::new(Arc::clone(&shape), request).map(|_| ()),
            Err(CreateError::Backend(BackendError(BackendId::Pclmul)))
        );
        assert_eq!(
            frozen.thaw(request).map(|_| ()),
            Err(BackendError(BackendId::Pclmul))
        );
        assert_eq!(
            super::detect::resolve(BackendRequest::Auto),
            Ok(BackendId::Portable)
        );
    });
    let expected = if std::is_x86_feature_detected!("pclmulqdq") {
        BackendId::Pclmul
    } else {
        BackendId::Portable
    };
    assert_eq!(super::detect::resolve(BackendRequest::Auto), Ok(expected));
    if expected == BackendId::Pclmul {
        assert!(Decoder::<Gf64>::new(request, 1).is_ok());
        assert!(MutableSketch::new(shape, request).is_ok());
        assert!(frozen.thaw(request).is_ok());
    }
}
