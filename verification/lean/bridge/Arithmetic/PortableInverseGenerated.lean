-- Exact declaration projection from reviewed checks-enabled original-source Aeneas output.
-- The original Portable inverse declaration below is retained verbatim.
-- Shared extracted types and function bodies are checked against Arithmetic.Funs.
module
public import Arithmetic.InverseUsingGenerated
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace bulksketch

/-- [bulksketch::backend::portable::{impl bulksketch::backend::contract::Arithmetic<F> for bulksketch::backend::portable::Portable}::inverse]:
    Source: 'src/backend/portable.rs', lines 26:4-32:5 -/
def backend.portable.Portable.Insts.BulksketchBackendContractArithmetic.inverse
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F) (a : Std.U64) :
  Result (Option Std.U64)
  := do
  field.maps.inverse fieldBinaryFieldInst a

end bulksketch
