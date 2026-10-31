#![forbid(unsafe_code)]

use {
    super::{
        BackendId, BackendRequest, DecodeExecution, Decoder, InsertDispatch, Pclmul, Portable,
        RowBudget, Toggle, Vpclmul512, detect,
    },
    crate::field::Gf64,
};

#[test]
fn auto_prefers_widest_checked_backend() {
    let scalar = std::is_x86_feature_detected!("pclmulqdq");
    let vector = scalar && detect::resolve(BackendRequest::Force(BackendId::Vpclmul512)).is_ok();
    let expected = if vector {
        BackendId::Vpclmul512
    } else if scalar {
        BackendId::Pclmul
    } else {
        BackendId::Portable
    };
    assert_eq!(detect::resolve(BackendRequest::Auto), Ok(expected));
    let decoder = Decoder::<Gf64>::new(BackendRequest::Auto, 1).unwrap();
    let execution = decoder.begin(RowBudget {
        nonzero: 2,
        total: 2,
    });
    assert!(match expected {
        BackendId::Vpclmul512 => matches!(execution, DecodeExecution::Vpclmul512(_)),
        BackendId::Pclmul => matches!(execution, DecodeExecution::Pclmul(_)),
        BackendId::Portable => matches!(execution, DecodeExecution::Portable(_)),
        BackendId::Vpclmul256 => unreachable!(),
    });
    let insertion = InsertDispatch::<Gf64>::new(expected);
    let toggle: Toggle<Gf64> = match expected {
        BackendId::Vpclmul512 => super::toggle::<Gf64, Vpclmul512>,
        BackendId::Pclmul => super::toggle::<Gf64, Pclmul>,
        BackendId::Portable => super::toggle::<Gf64, Portable>,
        BackendId::Vpclmul256 => unreachable!(),
    };
    assert!(std::ptr::fn_addr_eq(insertion.toggle, toggle));
    for (cpu, os) in [(false, true), (true, false)] {
        let _fixture = detect::vector_fixture(cpu, os);
        assert_eq!(
            detect::resolve(BackendRequest::Auto),
            Ok(if scalar {
                BackendId::Pclmul
            } else {
                BackendId::Portable
            })
        );
        assert!(Decoder::<Gf64>::new(BackendRequest::Force(BackendId::Vpclmul512), 1).is_err());
    }
    detect::without_pclmul(|| {
        assert_eq!(
            detect::resolve(BackendRequest::Auto),
            Ok(BackendId::Portable)
        );
        assert!(Decoder::<Gf64>::new(BackendRequest::Force(BackendId::Pclmul), 1).is_err());
        assert!(
            Decoder::<Gf64>::new(BackendRequest::Force(BackendId::Vpclmul512), 1).is_err(),
            "VP512 scalar arithmetic also requires PCLMUL"
        );
    });
}
