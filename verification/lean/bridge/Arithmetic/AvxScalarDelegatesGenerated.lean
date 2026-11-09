-- Original checked PCLMUL and AVX scalar delegation declarations.
import Arithmetic.X86PclmulNextGenerated
import Arithmetic.Funs

open Aeneas Aeneas.Std Result ControlFlow Error

namespace bulksketch

/-- [bulksketch::backend::x86_pclmul::{impl bulksketch::backend::contract::Arithmetic<F> for bulksketch::backend::x86_pclmul::Pclmul}::trace]:
    Source: 'src/backend/x86_pclmul.rs', lines 59:4-61:5 -/
def backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic.trace
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F) (a : Std.U64) :
  Result Std.U8
  := do
  field.maps.trace fieldBinaryFieldInst a

/-- [bulksketch::backend::x86_pclmul::{impl bulksketch::backend::contract::Arithmetic<F> for bulksketch::backend::x86_pclmul::Pclmul}::reduce]:
    Source: 'src/backend/x86_pclmul.rs', lines 73:4-75:5 -/
def backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic.reduce
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (product : types.RawProduct) :
  Result Std.U64
  := do
  field.gf64.reduce fieldBinaryFieldInst product

/-- [bulksketch::backend::x86_vpclmul512::{impl bulksketch::backend::contract::Arithmetic<F> for bulksketch::backend::x86_vpclmul512::Vpclmul512}::mul]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 50:4-52:5 -/
def
  backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractArithmetic.mul
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F) (a : Std.U64)
  (b : Std.U64) :
  Result Std.U64
  := do
  backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic.mul
    fieldBinaryFieldInst a b

/-- [bulksketch::backend::x86_vpclmul512::{impl bulksketch::backend::contract::Arithmetic<F> for bulksketch::backend::x86_vpclmul512::Vpclmul512}::square]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 53:4-55:5 -/
def
  backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractArithmetic.square
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F) (a : Std.U64) :
  Result Std.U64
  := do
  backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic.square
    fieldBinaryFieldInst a

/-- [bulksketch::backend::x86_vpclmul512::{impl bulksketch::backend::contract::Arithmetic<F> for bulksketch::backend::x86_vpclmul512::Vpclmul512}::frobenius]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 56:4-58:5 -/
def
  backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractArithmetic.frobenius
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F) (a : Std.U64)
  (power : Std.U32) :
  Result Std.U64
  := do
  backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic.frobenius
    fieldBinaryFieldInst a power

/-- [bulksketch::backend::x86_vpclmul512::{impl bulksketch::backend::contract::Arithmetic<F> for bulksketch::backend::x86_vpclmul512::Vpclmul512}::inverse]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 59:4-61:5 -/
def
  backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractArithmetic.inverse
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F) (a : Std.U64) :
  Result (Option Std.U64)
  := do
  backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic.inverse
    fieldBinaryFieldInst a

/-- [bulksketch::backend::x86_vpclmul512::{impl bulksketch::backend::contract::Arithmetic<F> for bulksketch::backend::x86_vpclmul512::Vpclmul512}::trace]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 62:4-64:5 -/
def
  backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractArithmetic.trace
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F) (a : Std.U64) :
  Result Std.U8
  := do
  backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic.trace
    fieldBinaryFieldInst a

/-- [bulksketch::backend::x86_vpclmul512::{impl bulksketch::backend::contract::Arithmetic<F> for bulksketch::backend::x86_vpclmul512::Vpclmul512}::solve_quadratic]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 65:4-67:5 -/
def
  backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractArithmetic.solve_quadratic
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F) (a : Std.U64) :
  Result (Option Std.U64)
  := do
  backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic.solve_quadratic
    fieldBinaryFieldInst a

/-- [bulksketch::backend::x86_vpclmul512::{impl bulksketch::backend::contract::Arithmetic<F> for bulksketch::backend::x86_vpclmul512::Vpclmul512}::raw_mul]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 68:4-70:5 -/
def
  backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractArithmetic.raw_mul
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F) (a : Std.U64)
  (b : Std.U64) :
  Result types.RawProduct
  := do
  backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic.raw_mul
    fieldBinaryFieldInst a b

/-- [bulksketch::backend::x86_vpclmul512::{impl bulksketch::backend::contract::Arithmetic<F> for bulksketch::backend::x86_vpclmul512::Vpclmul512}::reduce]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 71:4-73:5 -/
def
  backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractArithmetic.reduce
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (p : types.RawProduct) :
  Result Std.U64
  := do
  backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic.reduce
    fieldBinaryFieldInst p

end bulksketch
