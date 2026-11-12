module
public import Arithmetic.FunsExternal
@[expose] public section

namespace Aeneas.Std

/-- Reuse the complete checked conversion model for the original lookup's U32 index. -/
@[rust_fun "core::convert::num::ptr_try_from_impls::{core::convert::TryFrom<usize, u32, core::num::error::TryFromIntError>}::try_from"]
def Usize.Insts.CoreConvertTryFromU32TryFromIntError.try_from (word : U32) :
    Result (core.result.Result Usize core.num.error.TryFromIntError) :=
  core.num.tryFromUScalar .Usize word

end Aeneas.Std
