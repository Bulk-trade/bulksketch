-- Exact original AVX slice arithmetic entry declarations from checked stock extraction.
import Arithmetic.AvxSliceKernelGenerated
import Arithmetic.PortableSliceGenerated

open Aeneas Aeneas.Std Result ControlFlow Error

namespace bulksketch

variable (loadModel : AvxSquareRuntime.Load)
variable (storeModel : AvxSquareRuntime.Store)
variable (xorModel : AvxSliceKernelRuntime.Xor)

local notation "backend.x86_vpclmul512.scale_kernel" =>
  (backend.x86_vpclmul512.scale_kernel loadModel storeModel xorModel)
local notation "backend.x86_vpclmul512.square_kernel" =>
  (backend.x86_vpclmul512.square_kernel loadModel storeModel)

/-- [bulksketch::backend::x86_vpclmul512::scale_xor]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 316:0-318:1 -/
def backend.x86_vpclmul512.scale_xor
  (dst : Slice Std.U64) (src : Slice Std.U64) (scale : Std.U64) :
  Result (Slice Std.U64)
  := do
  backend.x86_vpclmul512.scale_kernel false dst src scale

local notation "backend.x86_vpclmul512.scale_xor" => (backend.x86_vpclmul512.scale_xor loadModel storeModel xorModel)

/-- [bulksketch::backend::x86_vpclmul512::{impl bulksketch::backend::contract::Arithmetic<F> for bulksketch::backend::x86_vpclmul512::Vpclmul512}::scale_xor]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 86:4-93:5 -/
def
  backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractArithmetic.scale_xor
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (dst : Slice Std.U64) (src : Slice Std.U64) (scale : Std.U64) :
  Result (Slice Std.U64)
  := do
  let left_val := Slice.len dst
  let right_val := Slice.len src
  if left_val = right_val
  then
    let i ← fieldBinaryFieldInst.BITS
    if i != 64#u32
    then
      backend.portable.Portable.Insts.BulksketchBackendContractArithmetic.scale_xor
        fieldBinaryFieldInst dst src scale
    else backend.x86_vpclmul512.scale_xor dst src scale
  else
    let _ ← core.fmt.Arguments.from_str (toStr "scale_xor length mismatch")
    fail panic

/-- [bulksketch::backend::x86_vpclmul512::square_slice]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 345:0-347:1 -/
def backend.x86_vpclmul512.square_slice
  (dst : Slice Std.U64) (src : Slice Std.U64) : Result (Slice Std.U64) := do
  backend.x86_vpclmul512.square_kernel false dst src

local notation "backend.x86_vpclmul512.square_slice" => (backend.x86_vpclmul512.square_slice loadModel storeModel)

/-- [bulksketch::backend::x86_vpclmul512::{impl bulksketch::backend::contract::Arithmetic<F> for bulksketch::backend::x86_vpclmul512::Vpclmul512}::square_slice]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 95:4-102:5 -/
def
  backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractArithmetic.square_slice
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (dst : Slice Std.U64) (src : Slice Std.U64) :
  Result (Slice Std.U64)
  := do
  let left_val := Slice.len dst
  let right_val := Slice.len src
  if left_val = right_val
  then
    let i ← fieldBinaryFieldInst.BITS
    if i != 64#u32
    then
      backend.portable.Portable.Insts.BulksketchBackendContractArithmetic.square_slice
        fieldBinaryFieldInst dst src
    else backend.x86_vpclmul512.square_slice dst src
  else
    let _ ←
      core.fmt.Arguments.from_str (toStr "square_slice length mismatch")
    fail panic

end bulksketch
