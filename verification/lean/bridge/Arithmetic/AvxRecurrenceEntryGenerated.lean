-- Original checked AVX odd_recurrence_matches backend entry.
import Arithmetic.AvxLinearEntryGenerated
import Arithmetic.AvxRecurrenceGenerated
import Arithmetic.OddRecurrenceGenerated

open Aeneas Aeneas.Std Result ControlFlow Error

namespace bulksketch

variable (loadModel : AvxSquareRuntime.Load)
variable (portableModel : {F : Type} → field.BinaryField F → backend.contract.BulkKernels backend.portable.Portable F)
local notation "backend.x86_vpclmul512.odd_recurrence_matches" =>
  (backend.x86_vpclmul512.odd_recurrence_matches loadModel)
local notation "backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels" => portableModel

/-- [bulksketch::backend::x86_vpclmul512::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::x86_vpclmul512::Vpclmul512}::odd_recurrence_matches]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 124:4-131:5 -/
def
  backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.odd_recurrence_matches
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (odd : Slice Std.U64) (squared_locator : Slice Std.U64) :
  Result Bool
  := do
  let i ← fieldBinaryFieldInst.BITS
  if i != 64#u32
  then
    backend.contract.BulkKernels.odd_recurrence_matches.default
      (backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels
      fieldBinaryFieldInst) odd squared_locator
  else backend.x86_vpclmul512.odd_recurrence_matches odd squared_locator

end bulksketch
