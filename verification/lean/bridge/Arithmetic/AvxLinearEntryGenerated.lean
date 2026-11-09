-- Original checked AVX multiply_linear backend entry.
import Arithmetic.AvxMultiplyLinearGenerated
import Arithmetic.SliceKernelGenerated

open Aeneas Aeneas.Std Result ControlFlow Error

namespace bulksketch

/-- [bulksketch::backend::portable::Portable]
    Source: 'src/backend/portable.rs', lines 11:0-11:27 -/
@[reducible]
def backend.portable.Portable := Unit

variable (loadModel : AvxSquareRuntime.Load) (storeModel : AvxSquareRuntime.Store)
variable (portableModel : {F : Type} → field.BinaryField F → backend.contract.BulkKernels backend.portable.Portable F)
local notation "backend.x86_vpclmul512.multiply_linear" =>
  (backend.x86_vpclmul512.multiply_linear loadModel storeModel)
local notation "backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels" => portableModel

/-- [bulksketch::backend::x86_vpclmul512::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::x86_vpclmul512::Vpclmul512}::multiply_linear]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 116:4-122:5 -/
def
  backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.multiply_linear
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (coefficients : Slice Std.U64) (root : Std.U64) :
  Result (Slice Std.U64)
  := do
  let i ← fieldBinaryFieldInst.BITS
  if i != 64#u32
  then
    backend.contract.BulkKernels.multiply_linear.default
      (backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels
      fieldBinaryFieldInst) coefficients root
  else backend.x86_vpclmul512.multiply_linear coefficients root

end bulksketch
