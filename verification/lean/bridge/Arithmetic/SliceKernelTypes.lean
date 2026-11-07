-- Exact original-source declaration projection. Imports are adapted only.
module
public import Arithmetic.Types
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

/-- Trait declaration: [bulksketch::backend::contract::Arithmetic]
    Source: 'src/backend/contract.rs', lines 8:0-47:1 -/
structure backend.contract.Arithmetic (Self : Type _) (F : Type _) where
  coremarkerCopyInst : core.marker.Copy Self
  fieldBinaryFieldInst : field.BinaryField F
  mul : Std.U64 → Std.U64 → Result Std.U64
  square : Std.U64 → Result Std.U64
  frobenius : Std.U64 → Std.U32 → Result Std.U64
  inverse : Std.U64 → Result (Option Std.U64)
  trace : Std.U64 → Result Std.U8
  solve_quadratic : Std.U64 → Result (Option Std.U64)
  raw_mul : Std.U64 → Std.U64 → Result types.RawProduct
  reduce : types.RawProduct → Result Std.U64
  scale_xor : Slice Std.U64 → Slice Std.U64 → Std.U64 → Result (Slice
    Std.U64)
  square_slice : Slice Std.U64 → Slice Std.U64 → Result (Slice Std.U64)

/-- Trait declaration: [bulksketch::backend::contract::BulkKernels]
    Source: 'src/backend/contract.rs', lines 50:0-121:1 -/
structure backend.contract.BulkKernels (Self : Type _) (F : Type _) where
  ArithmeticInst : backend.contract.Arithmetic Self F
  fieldBinaryFieldInst : field.BinaryField F
  square_mod : Slice Std.U64 → Slice Std.U64 → Slice Std.U64 → Slice
    types.RawProduct → Result (Bool × (Slice Std.U64) × (Slice
    types.RawProduct))
  multiply_linear : Slice Std.U64 → Std.U64 → Result (Slice Std.U64)
  odd_recurrence_matches : Slice Std.U64 → Slice Std.U64 → Result Bool
  insert_nonzero : Slice Std.U64 → Slice Std.U64 → Result (Slice Std.U64)
  encode_nonzero : Slice Std.U64 → Slice Std.U64 → Result (Slice Std.U64)
  xor_assign : Slice Std.U64 → Slice Std.U64 → Result (Slice Std.U64)
  difference : Slice Std.U64 → Slice Std.U64 → Slice Std.U8 → Result
    (Bool × (Slice Std.U64))
  horner_many : Slice Std.U64 → Slice Std.U64 → Slice Std.U64 → Result
    (Slice Std.U64)

end bulksketch
