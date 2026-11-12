-- Exact original AVX modular-square selector with its proved free callee.
import Arithmetic.AvxSquareGenerated

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace bulksketch

variable (loadModel : Aeneas.Std.AvxSquareRuntime.Load)
variable (storeModel : Aeneas.Std.AvxSquareRuntime.Store)

local notation "backend.x86_vpclmul512.square_mod" =>
  (backend.x86_vpclmul512.square_mod loadModel storeModel)

/-- [bulksketch::backend::x86_vpclmul512::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::x86_vpclmul512::Vpclmul512}::square_mod]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 106:4-114:5 -/
def
  backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.square_mod
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F) (a : Slice Std.U64)
  (table : Slice Std.U64) (dst : Slice Std.U64) (raw : Slice types.RawProduct)
  :
  Result (Bool × (Slice Std.U64) × (Slice types.RawProduct))
  := do
  let i ← fieldBinaryFieldInst.BITS
  if i != 64#u32
  then ok (false, dst, raw)
  else
    let (dst1, raw1) ← backend.x86_vpclmul512.square_mod a table dst raw
    ok (true, dst1, raw1)

end bulksketch
