-- Original stock-checked Affine selector declarations.
import Arithmetic.RootSetupGenerated
import Arithmetic.WorkScheduleRuntime
open Aeneas Aeneas.Std Result ControlFlow Error

namespace bulksketch

/-- [bulksketch::decode::affine::enumerate_preferred]:
    Source: 'src/decode/affine.rs', lines 86:0-95:1 -/
def decode.affine.enumerate_preferred
  (degree : Std.Usize) (rank : Std.Usize) : Result Bool := do
  let i ← lift (UScalar.cast .U32 rank)
  let o ← core.num.U64.checked_shl 1#u64 i
  match o with
  | none => ok false
  | some points =>
    let d ← lift (UScalar.cast .U64 degree)
    let i1 ← core.num.U64.div_ceil points 8#u64
    let i2 ← 6#u64 * d
    let o1 ← lift (U64.checked_mul i1 i2)
    match o1 with
    | none => ok false
    | some enumeration =>
      let i3 ← lift (UScalar.cast .U64 rank)
      let i4 ← decode.affine.square_products d
      let i5 ← i3 * i4
      let i6 ← 3#u64 * 28#u64
      let i7 ← i6 + 1#u64
      let i8 ← i7 * d
      let i9 ← i5 + i8
      ok (enumeration <= i9)

end bulksketch
