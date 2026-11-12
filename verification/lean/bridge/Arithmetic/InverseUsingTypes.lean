-- Exact declaration projection from the reviewed original-source extraction.
-- Only imports/type sharing are adapted; declarations below remain verbatim.
module
public import Arithmetic.Types
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

/-- [bulksketch::field::maps::inverse_using::{closure}]
    Source: 'src/field/maps.rs', lines 42:40-47:5 -/
@[reducible]
def field.maps.inverse_using.closure (F : Type _) (T1 : Type _) (T2 : Type _)
  :=
  T2

end bulksketch
