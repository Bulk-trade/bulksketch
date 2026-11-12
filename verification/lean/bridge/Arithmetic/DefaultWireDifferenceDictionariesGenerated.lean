-- Exact original Portable and PCLMUL trait dictionaries.
import Arithmetic.DefaultWireDifferenceGenerated
import Arithmetic.AvxLinearEntryGenerated
import Arithmetic.AvxScalarDelegatesGenerated
import Arithmetic.OddRecurrenceGenerated
import Arithmetic.PortableEncodingGenerated
import Arithmetic.PortableHornerGenerated
import Arithmetic.PortableInverseGenerated
import Arithmetic.PortableSliceGenerated
import Arithmetic.PortableXorGenerated
import Arithmetic.RowDispatchGenerated
import Arithmetic.X86PclmulHornerGenerated
import Arithmetic.X86PclmulInsertGenerated
import Arithmetic.X86PclmulNextGenerated
import Arithmetic.X86PclmulSliceGenerated

open Aeneas Aeneas.Std Result
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxRecDepth 2048
set_option maxHeartbeats 2000000

namespace bulksketch

/-- [bulksketch::backend::portable::{impl core::clone::Clone for bulksketch::backend::portable::Portable}::clone]:
    Source: 'src/backend/portable.rs', lines 10:9-10:14
    Visibility: public -/
def backend.portable.Portable.Insts.CoreCloneClone.clone
  (self : backend.portable.Portable) : Result backend.portable.Portable := do
  ok self

/-- Trait implementation: [bulksketch::backend::portable::{impl core::clone::Clone for bulksketch::backend::portable::Portable}]
    Source: 'src/backend/portable.rs', lines 10:9-10:14 -/
@[reducible]
def backend.portable.Portable.Insts.CoreCloneClone : core.clone.Clone
  backend.portable.Portable := {
  clone := backend.portable.Portable.Insts.CoreCloneClone.clone
}

/-- Trait implementation: [bulksketch::backend::portable::{impl core::marker::Copy for bulksketch::backend::portable::Portable}]
    Source: 'src/backend/portable.rs', lines 10:16-10:20 -/
@[reducible]
def backend.portable.Portable.Insts.CoreMarkerCopy : core.marker.Copy
  backend.portable.Portable := {
  cloneInst := backend.portable.Portable.Insts.CoreCloneClone
}

/-- Trait implementation: [bulksketch::backend::portable::{impl bulksketch::backend::contract::Arithmetic<F> for bulksketch::backend::portable::Portable}]
    Source: 'src/backend/portable.rs', lines 13:0-82:1 -/
@[reducible]
def backend.portable.Portable.Insts.BulksketchBackendContractArithmetic {F :
  Type _} (fieldBinaryFieldInst1 : field.BinaryField F) :
  backend.contract.Arithmetic backend.portable.Portable F := {
  coremarkerCopyInst := backend.portable.Portable.Insts.CoreMarkerCopy
  fieldBinaryFieldInst := fieldBinaryFieldInst1
  mul :=
    backend.portable.Portable.Insts.BulksketchBackendContractArithmetic.mul
    fieldBinaryFieldInst1
  square :=
    backend.portable.Portable.Insts.BulksketchBackendContractArithmetic.square
    fieldBinaryFieldInst1
  frobenius :=
    backend.portable.Portable.Insts.BulksketchBackendContractArithmetic.frobenius
    fieldBinaryFieldInst1
  inverse :=
    backend.portable.Portable.Insts.BulksketchBackendContractArithmetic.inverse
    fieldBinaryFieldInst1
  trace :=
    backend.portable.Portable.Insts.BulksketchBackendContractArithmetic.trace
    fieldBinaryFieldInst1
  solve_quadratic :=
    backend.portable.Portable.Insts.BulksketchBackendContractArithmetic.solve_quadratic
    fieldBinaryFieldInst1
  raw_mul :=
    backend.portable.Portable.Insts.BulksketchBackendContractArithmetic.raw_mul
    fieldBinaryFieldInst1
  reduce :=
    backend.portable.Portable.Insts.BulksketchBackendContractArithmetic.reduce
    fieldBinaryFieldInst1
  scale_xor :=
    backend.portable.Portable.Insts.BulksketchBackendContractArithmetic.scale_xor
    fieldBinaryFieldInst1
  square_slice :=
    backend.portable.Portable.Insts.BulksketchBackendContractArithmetic.square_slice
    fieldBinaryFieldInst1
}

/-- Trait implementation: [bulksketch::backend::portable::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::portable::Portable}]
    Source: 'src/backend/portable.rs', lines 84:0-121:1 -/
@[reducible]
impl_def backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels
  {F : Type _} (fieldBinaryFieldInst1 : field.BinaryField F) :
  backend.contract.BulkKernels backend.portable.Portable F := {
  ArithmeticInst :=
    backend.portable.Portable.Insts.BulksketchBackendContractArithmetic
    fieldBinaryFieldInst1
  fieldBinaryFieldInst := fieldBinaryFieldInst1
  square_mod := backend.contract.BulkKernels.square_mod.default
    backend.portable.Portable F
  multiply_linear := backend.contract.BulkKernels.multiply_linear.default
    (backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels
    fieldBinaryFieldInst1)
  odd_recurrence_matches :=
    backend.contract.BulkKernels.odd_recurrence_matches.default
    (backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels
    fieldBinaryFieldInst1)
  insert_nonzero :=
    backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.insert_nonzero
    fieldBinaryFieldInst1
  encode_nonzero := backend.contract.BulkKernels.encode_nonzero.default
    (backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels
    fieldBinaryFieldInst1)
  xor_assign :=
    backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.xor_assign
    fieldBinaryFieldInst1
  difference := backend.contract.BulkKernels.difference.default
    backend.portable.Portable F
  horner_many :=
    backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.horner_many
    fieldBinaryFieldInst1
}

/-- [bulksketch::backend::x86_pclmul::{impl core::clone::Clone for bulksketch::backend::x86_pclmul::Pclmul}::clone]:
    Source: 'src/backend/x86_pclmul.rs', lines 18:9-18:14
    Visibility: public -/
def backend.x86_pclmul.Pclmul.Insts.CoreCloneClone.clone
  (self : backend.x86_pclmul.Pclmul) : Result backend.x86_pclmul.Pclmul := do
  ok self

/-- Trait implementation: [bulksketch::backend::x86_pclmul::{impl core::clone::Clone for bulksketch::backend::x86_pclmul::Pclmul}]
    Source: 'src/backend/x86_pclmul.rs', lines 18:9-18:14 -/
@[reducible]
def backend.x86_pclmul.Pclmul.Insts.CoreCloneClone : core.clone.Clone
  backend.x86_pclmul.Pclmul := {
  clone := backend.x86_pclmul.Pclmul.Insts.CoreCloneClone.clone
}

/-- Trait implementation: [bulksketch::backend::x86_pclmul::{impl core::marker::Copy for bulksketch::backend::x86_pclmul::Pclmul}]
    Source: 'src/backend/x86_pclmul.rs', lines 18:16-18:20 -/
@[reducible]
def backend.x86_pclmul.Pclmul.Insts.CoreMarkerCopy : core.marker.Copy
  backend.x86_pclmul.Pclmul := {
  cloneInst := backend.x86_pclmul.Pclmul.Insts.CoreCloneClone
}

/-- Trait implementation: [bulksketch::backend::x86_pclmul::{impl bulksketch::backend::contract::Arithmetic<F> for bulksketch::backend::x86_pclmul::Pclmul}]
    Source: 'src/backend/x86_pclmul.rs', lines 34:0-95:1 -/
@[reducible]
def backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic {F :
  Type _} (fieldBinaryFieldInst1 : field.BinaryField F) :
  backend.contract.Arithmetic backend.x86_pclmul.Pclmul F := {
  coremarkerCopyInst := backend.x86_pclmul.Pclmul.Insts.CoreMarkerCopy
  fieldBinaryFieldInst := fieldBinaryFieldInst1
  mul :=
    backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic.mul
    fieldBinaryFieldInst1
  square :=
    backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic.square
    fieldBinaryFieldInst1
  frobenius :=
    backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic.frobenius
    fieldBinaryFieldInst1
  inverse :=
    backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic.inverse
    fieldBinaryFieldInst1
  trace :=
    backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic.trace
    fieldBinaryFieldInst1
  solve_quadratic :=
    backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic.solve_quadratic
    fieldBinaryFieldInst1
  raw_mul :=
    backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic.raw_mul
    fieldBinaryFieldInst1
  reduce :=
    backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic.reduce
    fieldBinaryFieldInst1
  scale_xor :=
    backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic.scale_xor
    fieldBinaryFieldInst1
  square_slice :=
    backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic.square_slice
    fieldBinaryFieldInst1
}

/-- Trait implementation: [bulksketch::backend::x86_pclmul::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::x86_pclmul::Pclmul}]
    Source: 'src/backend/x86_pclmul.rs', lines 97:0-115:1 -/
@[reducible]
impl_def backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractBulkKernels
  {F : Type _} (fieldBinaryFieldInst1 : field.BinaryField F) :
  backend.contract.BulkKernels backend.x86_pclmul.Pclmul F := {
  ArithmeticInst :=
    backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic
    fieldBinaryFieldInst1
  fieldBinaryFieldInst := fieldBinaryFieldInst1
  square_mod := backend.contract.BulkKernels.square_mod.default
    backend.x86_pclmul.Pclmul F
  multiply_linear := backend.contract.BulkKernels.multiply_linear.default
    (backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractBulkKernels
    fieldBinaryFieldInst1)
  odd_recurrence_matches :=
    backend.contract.BulkKernels.odd_recurrence_matches.default
    (backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractBulkKernels
    fieldBinaryFieldInst1)
  insert_nonzero :=
    backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractBulkKernels.insert_nonzero
    fieldBinaryFieldInst1
  encode_nonzero := backend.contract.BulkKernels.encode_nonzero.default
    (backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractBulkKernels
    fieldBinaryFieldInst1)
  xor_assign :=
    backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractBulkKernels.xor_assign
    fieldBinaryFieldInst1
  difference := backend.contract.BulkKernels.difference.default
    backend.x86_pclmul.Pclmul F
  horner_many :=
    backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractBulkKernels.horner_many
    fieldBinaryFieldInst1
}

end bulksketch
