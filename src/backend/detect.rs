//! Availability of built arithmetic paths; operation selection belongs to the sketch dispatcher.
#![forbid(unsafe_code)]

use crate::types::{BackendError, BackendId, BackendRequest};

#[inline]
pub(crate) fn resolve(request: BackendRequest) -> Result<BackendId, BackendError> {
    match request {
        BackendRequest::Auto => Ok(if vpclmul512_available() {
            BackendId::Vpclmul512
        } else if pclmul_available() {
            BackendId::Pclmul
        } else {
            BackendId::Portable
        }),
        BackendRequest::Force(BackendId::Portable) => Ok(BackendId::Portable),
        BackendRequest::Force(BackendId::Pclmul) if pclmul_available() => Ok(BackendId::Pclmul),
        BackendRequest::Force(BackendId::Vpclmul512) if vpclmul512_available() => {
            Ok(BackendId::Vpclmul512)
        }
        BackendRequest::Force(id) => Err(BackendError(id)),
    }
}

fn vpclmul512_available() -> bool {
    #[cfg(target_arch = "x86_64")]
    let available = pclmul_available() && super::x86_vpclmul512::available();
    #[cfg(not(target_arch = "x86_64"))]
    let available = false;
    #[cfg(test)]
    let available = available && TEST_VECTOR_ENABLED.with(std::cell::Cell::get);
    available
}

fn pclmul_available() -> bool {
    // Legacy PCLMUL uses XMM/SSE state, architectural on x86-64. No AVX/YMM/ZMM
    // state is used, so an additional OSXSAVE/XGETBV gate is unnecessary.
    #[cfg(target_arch = "x86_64")]
    let available = std::is_x86_feature_detected!("pclmulqdq");
    #[cfg(not(target_arch = "x86_64"))]
    let available = false;
    #[cfg(test)]
    let available = available && !DISABLE_PCLMUL.with(std::cell::Cell::get);
    available
}

#[cfg(test)]
std::thread_local! {
    static DISABLE_PCLMUL: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

#[cfg(all(test, target_arch = "x86_64"))]
pub(crate) fn without_pclmul<T>(run: impl FnOnce() -> T) -> T {
    struct Restore<'a>(&'a std::cell::Cell<bool>, bool);
    impl Drop for Restore<'_> {
        fn drop(&mut self) {
            self.0.set(self.1);
        }
    }
    DISABLE_PCLMUL.with(|disabled| {
        let _restore = Restore(disabled, disabled.replace(true));
        run()
    })
}

#[cfg(test)]
thread_local! { static TEST_VECTOR_ENABLED: std::cell::Cell<bool> = const { std::cell::Cell::new(true) }; }

#[cfg(test)]
pub(crate) struct WithoutVector {
    vector: bool,
    scalar_disabled: bool,
}

#[cfg(test)]
impl Drop for WithoutVector {
    fn drop(&mut self) {
        TEST_VECTOR_ENABLED.with(|enabled| enabled.set(self.vector));
        DISABLE_PCLMUL.with(|disabled| disabled.set(self.scalar_disabled));
    }
}

#[cfg(test)]
pub(crate) fn without_vector() -> WithoutVector {
    let fixture = vector_fixture(false, false);
    DISABLE_PCLMUL.with(|disabled| disabled.set(true));
    fixture
}

#[cfg(test)]
pub(crate) fn vector_fixture(cpu: bool, os: bool) -> WithoutVector {
    WithoutVector {
        vector: TEST_VECTOR_ENABLED.with(|enabled| enabled.replace(vpclmul512_supported(cpu, os))),
        scalar_disabled: DISABLE_PCLMUL.with(std::cell::Cell::get),
    }
}

#[cfg(any(target_arch = "x86_64", test))]
pub(super) fn vpclmul512_supported(cpu: bool, os: bool) -> bool {
    cpu && os
}
