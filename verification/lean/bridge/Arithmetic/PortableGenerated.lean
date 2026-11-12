-- Exact declaration projection from successful original-source Aeneas output.
-- All seven Portable method declarations below are retained verbatim.
-- Shared extracted types and function bodies are checked against Arithmetic.Funs.
module
public import Arithmetic.Funs
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace bulksketch

/-- [bulksketch::backend::portable::{impl bulksketch::backend::contract::Arithmetic<F> for bulksketch::backend::portable::Portable}::mul]:
    Source: 'src/backend/portable.rs', lines 14:4-16:5 -/
def backend.portable.Portable.Insts.BulksketchBackendContractArithmetic.mul
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F) (a : Std.U64)
  (b : Std.U64) :
  Result Std.U64
  := do
  field.gf64.mul fieldBinaryFieldInst a b

/-- [bulksketch::backend::portable::{impl bulksketch::backend::contract::Arithmetic<F> for bulksketch::backend::portable::Portable}::square]:
    Source: 'src/backend/portable.rs', lines 18:4-20:5 -/
def backend.portable.Portable.Insts.BulksketchBackendContractArithmetic.square
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F) (a : Std.U64) :
  Result Std.U64
  := do
  field.gf64.square fieldBinaryFieldInst a

/-- [bulksketch::backend::portable::{impl bulksketch::backend::contract::Arithmetic<F> for bulksketch::backend::portable::Portable}::frobenius]:
    Source: 'src/backend/portable.rs', lines 22:4-24:5 -/
def
  backend.portable.Portable.Insts.BulksketchBackendContractArithmetic.frobenius
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F) (a : Std.U64)
  (power : Std.U32) :
  Result Std.U64
  := do
  field.gf64.frobenius fieldBinaryFieldInst a power

/-- [bulksketch::backend::portable::{impl bulksketch::backend::contract::Arithmetic<F> for bulksketch::backend::portable::Portable}::trace]:
    Source: 'src/backend/portable.rs', lines 34:4-36:5 -/
def backend.portable.Portable.Insts.BulksketchBackendContractArithmetic.trace
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F) (a : Std.U64) :
  Result Std.U8
  := do
  field.maps.trace fieldBinaryFieldInst a

/-- [bulksketch::backend::portable::{impl bulksketch::backend::contract::Arithmetic<F> for bulksketch::backend::portable::Portable}::solve_quadratic]:
    Source: 'src/backend/portable.rs', lines 38:4-40:5 -/
def
  backend.portable.Portable.Insts.BulksketchBackendContractArithmetic.solve_quadratic
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F) (a : Std.U64) :
  Result (Option Std.U64)
  := do
  field.maps.solve_quadratic fieldBinaryFieldInst a

/-- [bulksketch::backend::portable::{impl bulksketch::backend::contract::Arithmetic<F> for bulksketch::backend::portable::Portable}::raw_mul]:
    Source: 'src/backend/portable.rs', lines 42:4-44:5 -/
def backend.portable.Portable.Insts.BulksketchBackendContractArithmetic.raw_mul
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F) (a : Std.U64)
  (b : Std.U64) :
  Result types.RawProduct
  := do
  field.gf64.raw_mul fieldBinaryFieldInst a b

/-- [bulksketch::backend::portable::{impl bulksketch::backend::contract::Arithmetic<F> for bulksketch::backend::portable::Portable}::reduce]:
    Source: 'src/backend/portable.rs', lines 46:4-48:5 -/
def backend.portable.Portable.Insts.BulksketchBackendContractArithmetic.reduce
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (product : types.RawProduct) :
  Result Std.U64
  := do
  field.gf64.reduce fieldBinaryFieldInst product

end bulksketch
