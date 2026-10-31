//! Arithmetic capabilities and canonical-word kernels only.
#![deny(unsafe_code)]

pub(crate) mod contract;
pub(crate) mod detect;
pub(crate) mod portable;
#[cfg(target_arch = "x86_64")]
pub(crate) mod x86_pclmul;

#[cfg(target_arch = "x86_64")]
pub(crate) mod x86_vpclmul512;

#[cfg(all(test, target_arch = "x86_64"))]
mod vpclmul512_tests;

#[cfg(all(test, target_arch = "x86_64"))]
mod pclmul_tests;
#[cfg(test)]
mod portable_tests;

#[cfg(test)]
mod difference_tests;

#[cfg(test)]
pub(crate) mod test_observer;

#[cfg(test)]
mod byte_map_tests;
