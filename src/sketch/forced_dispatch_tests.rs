#![forbid(unsafe_code)]

use {
    crate::{
        BackendError, BackendId, BackendRequest, CreateError, Decoder, Gf64, MutableSketch,
        ShapeLimits, SketchShape,
    },
    std::sync::Arc,
};

#[test]
fn force_checks_cpu_and_os_state() {
    let shape = Arc::new(
        SketchShape::<Gf64>::new(
            &[18],
            &ShapeLimits {
                max_wire_bytes: 200,
                max_buckets: 1,
                max_capacity_per_bucket: 18,
                max_total_syndrome_words: 18,
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
    let request = BackendRequest::Force(BackendId::Vpclmul512);
    for (cpu, os) in [(false, false), (false, true), (true, false)] {
        let _fixture = crate::backend::detect::vector_fixture(cpu, os);
        assert_eq!(
            MutableSketch::new(Arc::clone(&shape), request).map(|_| ()),
            Err(CreateError::Backend(BackendError(BackendId::Vpclmul512))),
            "cpu={cpu} os={os}"
        );
        assert_eq!(
            frozen.thaw(request).map(|_| ()),
            Err(BackendError(BackendId::Vpclmul512)),
            "thaw cpu={cpu} os={os}"
        );
        assert!(
            matches!(
                Decoder::<Gf64>::new(request, 1),
                Err(BackendError(BackendId::Vpclmul512))
            ),
            "decoder cpu={cpu} os={os}"
        );
    }
}
