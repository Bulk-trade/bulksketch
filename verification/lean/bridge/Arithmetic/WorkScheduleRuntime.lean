module
public import Aeneas
@[expose] public section

namespace Aeneas.Std

/-! Concrete standard-library bindings used by the original work schedule.
These definitions retain the unsigned conversion range check and the exact
shift-amount guard. Rust standard-library correspondence remains part of the
bridge trust boundary. -/

@[rust_fun "core::convert::num::ptr_try_from_impls::{core::convert::TryFrom<u64, usize, core::num::error::TryFromIntError>}::try_from"]
def U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from (value : Usize) :
    Result (core.result.Result U64 core.num.error.TryFromIntError) :=
  core.num.tryFromUScalar .U64 value

@[rust_fun "core::num::{u64}::checked_shl"]
def core.num.U64.checked_shl (value : U64) (amount : U32) : Result (Option U64) :=
  .ok (if amount.val < 64 then some ⟨value.bv <<< amount.val⟩ else none)

end Aeneas.Std
