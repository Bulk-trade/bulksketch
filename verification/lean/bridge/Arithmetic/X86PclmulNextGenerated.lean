-- Exact original PCLMUL maps declarations and verified generated dependencies.
import Arithmetic.X86PclmulGenerated
import Arithmetic.FrobeniusTablesGenerated
import Arithmetic.InverseGenerated

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace bulksketch

/-- [bulksketch::backend::x86_pclmul::inverse::{closure#2}]
    Source: 'src/backend/x86_pclmul.rs', lines 280:15-280:92 -/
@[reducible]
def backend.x86_pclmul.inverse.closure_2 (F : Type _) := Unit

/-- [bulksketch::backend::x86_pclmul::inverse::{closure#1}]
    Source: 'src/backend/x86_pclmul.rs', lines 269:12-269:66 -/
@[reducible]
def backend.x86_pclmul.inverse.closure_1 (F : Type _) := Unit

/-- [bulksketch::backend::x86_pclmul::inverse::{closure}]
    Source: 'src/backend/x86_pclmul.rs', lines 267:12-267:69 -/
@[reducible]
def backend.x86_pclmul.inverse.closure (F : Type _) := Unit

/-- [bulksketch::backend::x86_pclmul::frobenius]: loop body 0:
    Source: 'src/backend/x86_pclmul.rs', lines 254:4-257:5 -/
@[rust_loop_body]
def backend.x86_pclmul.frobenius_loop0.body
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (iter : core.ops.range.Range Std.U32) (a : Std.U64) :
  Result (ControlFlow ((core.ops.range.Range Std.U32) × Std.U64) Std.U64)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
  match o with
  | none => ok (done a)
  | some _ =>
    let a1 ← backend.x86_pclmul.multiply false fieldBinaryFieldInst a a
    ok (cont (iter1, a1))

/-- [bulksketch::backend::x86_pclmul::frobenius]: loop 0:
    Source: 'src/backend/x86_pclmul.rs', lines 254:4-257:5 -/
@[rust_loop]
def backend.x86_pclmul.frobenius_loop0
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (iter : core.ops.range.Range Std.U32) (a : Std.U64) :
  Result Std.U64
  := do
  loop
    (fun (iter1, a1) => backend.x86_pclmul.frobenius_loop0.body
      fieldBinaryFieldInst iter1 a1)
    (iter, a)

/-- [bulksketch::backend::x86_pclmul::frobenius]: loop body 1:
    Source: 'src/backend/x86_pclmul.rs', lines 254:4-257:5 -/
@[rust_loop_body]
def backend.x86_pclmul.frobenius_loop1.body
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (iter : core.ops.range.Range Std.U32) (a : Std.U64) :
  Result (ControlFlow ((core.ops.range.Range Std.U32) × Std.U64) Std.U64)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
  match o with
  | none => ok (done a)
  | some _ =>
    let a1 ← backend.x86_pclmul.multiply false fieldBinaryFieldInst a a
    ok (cont (iter1, a1))

/-- [bulksketch::backend::x86_pclmul::frobenius]: loop 1:
    Source: 'src/backend/x86_pclmul.rs', lines 254:4-257:5 -/
@[rust_loop]
def backend.x86_pclmul.frobenius_loop1
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (iter : core.ops.range.Range Std.U32) (a : Std.U64) :
  Result Std.U64
  := do
  loop
    (fun (iter1, a1) => backend.x86_pclmul.frobenius_loop1.body
      fieldBinaryFieldInst iter1 a1)
    (iter, a)

/-- [bulksketch::backend::x86_pclmul::frobenius]:
    Source: 'src/backend/x86_pclmul.rs', lines 248:0-259:1 -/
def backend.x86_pclmul.frobenius
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F) (a : Std.U64)
  (power : Std.U32) :
  Result Std.U64
  := do
  let i ← fieldBinaryFieldInst.BITS
  if i = 64#u32
  then
    let i1 ← power % i
    let o ← field.frobenius.lookup a i1
    match o with
    | none =>
      let i2 ← power % i
      backend.x86_pclmul.frobenius_loop0 fieldBinaryFieldInst
        { start := 0#u32, «end» := i2 } a
    | some value => ok value
  else
    let i1 ← power % i
    backend.x86_pclmul.frobenius_loop1 fieldBinaryFieldInst
      { start := 0#u32, «end» := i1 } a

/-- [bulksketch::backend::x86_pclmul::{impl bulksketch::backend::contract::Arithmetic<F> for bulksketch::backend::x86_pclmul::Pclmul}::frobenius]:
    Source: 'src/backend/x86_pclmul.rs', lines 45:4-48:5 -/
def
  backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic.frobenius
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F) (a : Std.U64)
  (power : Std.U32) :
  Result Std.U64
  := do
  backend.x86_pclmul.frobenius fieldBinaryFieldInst a power

/-- [bulksketch::backend::x86_pclmul::inverse::{impl core::ops::function::Fn<(u64,), u64> for bulksketch::backend::x86_pclmul::inverse::{closure#2}<F>}::call]:
    Source: 'src/backend/x86_pclmul.rs', lines 280:15-280:92 -/
def
  backend.x86_pclmul.inverse.closure_2.Insts.CoreOpsFunctionFnTupleU64U64.call
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (c : backend.x86_pclmul.inverse.closure_2 F) (tupled_args : Std.U64) :
  Result Std.U64
  := do
  let o ← field.frobenius.lookup tupled_args 7#u32
  core.option.Option.expect o (toStr "fixed inverse map")

/-- [bulksketch::backend::x86_pclmul::inverse::{impl core::ops::function::Fn<(u64, u32), u64> for bulksketch::backend::x86_pclmul::inverse::{closure#1}<F>}::call]:
    Source: 'src/backend/x86_pclmul.rs', lines 269:12-269:66 -/
def
  backend.x86_pclmul.inverse.closure_1.Insts.CoreOpsFunctionFnPairU64U32U64.call
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (c : backend.x86_pclmul.inverse.closure_1 F)
  (tupled_args : (Std.U64 × Std.U32)) :
  Result Std.U64
  := do
  let (value, power) := tupled_args
  backend.x86_pclmul.frobenius fieldBinaryFieldInst value power

/-- [bulksketch::backend::x86_pclmul::inverse::{impl core::ops::function::FnMut<(u64, u32), u64> for bulksketch::backend::x86_pclmul::inverse::{closure#1}<F>}::call_mut]:
    Source: 'src/backend/x86_pclmul.rs', lines 269:12-269:66 -/
def
  backend.x86_pclmul.inverse.closure_1.Insts.CoreOpsFunctionFnMutPairU64U32U64.call_mut
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (state : backend.x86_pclmul.inverse.closure_1 F)
  (args : (Std.U64 × Std.U32)) :
  Result (Std.U64 × (backend.x86_pclmul.inverse.closure_1 F))
  := do
  let i ←
    backend.x86_pclmul.inverse.closure_1.Insts.CoreOpsFunctionFnPairU64U32U64.call
      fieldBinaryFieldInst state args
  ok (i, state)

/-- [bulksketch::backend::x86_pclmul::inverse::{impl core::ops::function::FnOnce<(u64, u32), u64> for bulksketch::backend::x86_pclmul::inverse::{closure#1}<F>}::call_once]:
    Source: 'src/backend/x86_pclmul.rs', lines 269:12-269:66 -/
def
  backend.x86_pclmul.inverse.closure_1.Insts.CoreOpsFunctionFnOncePairU64U32U64.call_once
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (c : backend.x86_pclmul.inverse.closure_1 F) (p : (Std.U64 × Std.U32)) :
  Result Std.U64
  := do
  let (i, _) ←
    backend.x86_pclmul.inverse.closure_1.Insts.CoreOpsFunctionFnMutPairU64U32U64.call_mut
      fieldBinaryFieldInst c p
  ok i

/-- Trait implementation: [bulksketch::backend::x86_pclmul::inverse::{impl core::ops::function::FnOnce<(u64, u32), u64> for bulksketch::backend::x86_pclmul::inverse::{closure#1}<F>}]
    Source: 'src/backend/x86_pclmul.rs', lines 269:12-269:66 -/
@[reducible]
def
  backend.x86_pclmul.inverse.closure_1.Insts.CoreOpsFunctionFnOncePairU64U32U64
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F) :
  core.ops.function.FnOnce (backend.x86_pclmul.inverse.closure_1 F) (Std.U64 ×
  Std.U32) Std.U64 := {
  call_once :=
    backend.x86_pclmul.inverse.closure_1.Insts.CoreOpsFunctionFnOncePairU64U32U64.call_once
    fieldBinaryFieldInst
}

/-- Trait implementation: [bulksketch::backend::x86_pclmul::inverse::{impl core::ops::function::FnMut<(u64, u32), u64> for bulksketch::backend::x86_pclmul::inverse::{closure#1}<F>}]
    Source: 'src/backend/x86_pclmul.rs', lines 269:12-269:66 -/
@[reducible]
def
  backend.x86_pclmul.inverse.closure_1.Insts.CoreOpsFunctionFnMutPairU64U32U64
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F) :
  core.ops.function.FnMut (backend.x86_pclmul.inverse.closure_1 F) (Std.U64 ×
  Std.U32) Std.U64 := {
  FnOnceInst :=
    backend.x86_pclmul.inverse.closure_1.Insts.CoreOpsFunctionFnOncePairU64U32U64
    fieldBinaryFieldInst
  call_mut :=
    backend.x86_pclmul.inverse.closure_1.Insts.CoreOpsFunctionFnMutPairU64U32U64.call_mut
    fieldBinaryFieldInst
}

/-- Trait implementation: [bulksketch::backend::x86_pclmul::inverse::{impl core::ops::function::Fn<(u64, u32), u64> for bulksketch::backend::x86_pclmul::inverse::{closure#1}<F>}]
    Source: 'src/backend/x86_pclmul.rs', lines 269:12-269:66 -/
@[reducible]
def backend.x86_pclmul.inverse.closure_1.Insts.CoreOpsFunctionFnPairU64U32U64
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F) :
  core.ops.function.Fn (backend.x86_pclmul.inverse.closure_1 F) (Std.U64 ×
  Std.U32) Std.U64 := {
  FnMutInst :=
    backend.x86_pclmul.inverse.closure_1.Insts.CoreOpsFunctionFnMutPairU64U32U64
    fieldBinaryFieldInst
  call :=
    backend.x86_pclmul.inverse.closure_1.Insts.CoreOpsFunctionFnPairU64U32U64.call
    fieldBinaryFieldInst
}

/-- [bulksketch::backend::x86_pclmul::inverse::{impl core::ops::function::Fn<(u64, u64), u64> for bulksketch::backend::x86_pclmul::inverse::{closure}<F>}::call]:
    Source: 'src/backend/x86_pclmul.rs', lines 267:12-267:69 -/
def
  backend.x86_pclmul.inverse.closure.Insts.CoreOpsFunctionFnPairU64U64U64.call
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (c : backend.x86_pclmul.inverse.closure F)
  (tupled_args : (Std.U64 × Std.U64)) :
  Result Std.U64
  := do
  let (left, right) := tupled_args
  backend.x86_pclmul.multiply true fieldBinaryFieldInst left right

/-- [bulksketch::backend::x86_pclmul::inverse::{impl core::ops::function::FnMut<(u64, u64), u64> for bulksketch::backend::x86_pclmul::inverse::{closure}<F>}::call_mut]:
    Source: 'src/backend/x86_pclmul.rs', lines 267:12-267:69 -/
def
  backend.x86_pclmul.inverse.closure.Insts.CoreOpsFunctionFnMutPairU64U64U64.call_mut
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (state : backend.x86_pclmul.inverse.closure F) (args : (Std.U64 × Std.U64))
  :
  Result (Std.U64 × (backend.x86_pclmul.inverse.closure F))
  := do
  let i ←
    backend.x86_pclmul.inverse.closure.Insts.CoreOpsFunctionFnPairU64U64U64.call
      fieldBinaryFieldInst state args
  ok (i, state)

/-- [bulksketch::backend::x86_pclmul::inverse::{impl core::ops::function::FnOnce<(u64, u64), u64> for bulksketch::backend::x86_pclmul::inverse::{closure}<F>}::call_once]:
    Source: 'src/backend/x86_pclmul.rs', lines 267:12-267:69 -/
def
  backend.x86_pclmul.inverse.closure.Insts.CoreOpsFunctionFnOncePairU64U64U64.call_once
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (c : backend.x86_pclmul.inverse.closure F) (p : (Std.U64 × Std.U64)) :
  Result Std.U64
  := do
  let (i, _) ←
    backend.x86_pclmul.inverse.closure.Insts.CoreOpsFunctionFnMutPairU64U64U64.call_mut
      fieldBinaryFieldInst c p
  ok i

/-- Trait implementation: [bulksketch::backend::x86_pclmul::inverse::{impl core::ops::function::FnOnce<(u64, u64), u64> for bulksketch::backend::x86_pclmul::inverse::{closure}<F>}]
    Source: 'src/backend/x86_pclmul.rs', lines 267:12-267:69 -/
@[reducible]
def backend.x86_pclmul.inverse.closure.Insts.CoreOpsFunctionFnOncePairU64U64U64
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F) :
  core.ops.function.FnOnce (backend.x86_pclmul.inverse.closure F) (Std.U64 ×
  Std.U64) Std.U64 := {
  call_once :=
    backend.x86_pclmul.inverse.closure.Insts.CoreOpsFunctionFnOncePairU64U64U64.call_once
    fieldBinaryFieldInst
}

/-- Trait implementation: [bulksketch::backend::x86_pclmul::inverse::{impl core::ops::function::FnMut<(u64, u64), u64> for bulksketch::backend::x86_pclmul::inverse::{closure}<F>}]
    Source: 'src/backend/x86_pclmul.rs', lines 267:12-267:69 -/
@[reducible]
def backend.x86_pclmul.inverse.closure.Insts.CoreOpsFunctionFnMutPairU64U64U64
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F) :
  core.ops.function.FnMut (backend.x86_pclmul.inverse.closure F) (Std.U64 ×
  Std.U64) Std.U64 := {
  FnOnceInst :=
    backend.x86_pclmul.inverse.closure.Insts.CoreOpsFunctionFnOncePairU64U64U64
    fieldBinaryFieldInst
  call_mut :=
    backend.x86_pclmul.inverse.closure.Insts.CoreOpsFunctionFnMutPairU64U64U64.call_mut
    fieldBinaryFieldInst
}

/-- Trait implementation: [bulksketch::backend::x86_pclmul::inverse::{impl core::ops::function::Fn<(u64, u64), u64> for bulksketch::backend::x86_pclmul::inverse::{closure}<F>}]
    Source: 'src/backend/x86_pclmul.rs', lines 267:12-267:69 -/
@[reducible]
def backend.x86_pclmul.inverse.closure.Insts.CoreOpsFunctionFnPairU64U64U64 {F
  : Type _} (fieldBinaryFieldInst : field.BinaryField F) : core.ops.function.Fn
  (backend.x86_pclmul.inverse.closure F) (Std.U64 × Std.U64) Std.U64 := {
  FnMutInst :=
    backend.x86_pclmul.inverse.closure.Insts.CoreOpsFunctionFnMutPairU64U64U64
    fieldBinaryFieldInst
  call :=
    backend.x86_pclmul.inverse.closure.Insts.CoreOpsFunctionFnPairU64U64U64.call
    fieldBinaryFieldInst
}

/-- [bulksketch::backend::x86_pclmul::inverse]:
    Source: 'src/backend/x86_pclmul.rs', lines 262:0-295:1 -/
def backend.x86_pclmul.inverse
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F) (a : Std.U64) :
  Result (Option Std.U64)
  := do
  let i ← fieldBinaryFieldInst.BITS
  if i != 64#u32
  then
    field.maps.inverse_with_frobenius fieldBinaryFieldInst
      (backend.x86_pclmul.inverse.closure.Insts.CoreOpsFunctionFnPairU64U64U64
      fieldBinaryFieldInst)
      (backend.x86_pclmul.inverse.closure_1.Insts.CoreOpsFunctionFnPairU64U32U64
      fieldBinaryFieldInst) a () ()
  else
    if a = 0#u64
    then ok none
    else
      if a = 1#u64
      then ok (some 1#u64)
      else
        let i1 ← backend.x86_pclmul.multiply false fieldBinaryFieldInst a a
        let t2 ← backend.x86_pclmul.multiply true fieldBinaryFieldInst i1 a
        let i2 ← backend.x86_pclmul.multiply false fieldBinaryFieldInst t2 t2
        let t3 ← backend.x86_pclmul.multiply true fieldBinaryFieldInst i2 a
        let o ← field.frobenius.lookup t3 3#u32
        let f3 ← core.option.Option.expect o (toStr "fixed inverse map")
        let t6 ← backend.x86_pclmul.multiply true fieldBinaryFieldInst f3 t3
        let i3 ← backend.x86_pclmul.multiply false fieldBinaryFieldInst t6 t6
        let t7 ← backend.x86_pclmul.multiply true fieldBinaryFieldInst i3 a
        let i4 ←
          backend.x86_pclmul.inverse.closure_2.Insts.CoreOpsFunctionFnTupleU64U64.call
            fieldBinaryFieldInst () t7
        let t14 ← backend.x86_pclmul.multiply true fieldBinaryFieldInst i4 t7
        let i5 ←
          backend.x86_pclmul.inverse.closure_2.Insts.CoreOpsFunctionFnTupleU64U64.call
            fieldBinaryFieldInst () t14
        let t21 ← backend.x86_pclmul.multiply true fieldBinaryFieldInst i5 t7
        let i6 ← field.frobenius.inverse21 t21
        let t42 ←
          backend.x86_pclmul.multiply true fieldBinaryFieldInst i6 t21
        let i7 ← field.frobenius.inverse21 t42
        let t63 ←
          backend.x86_pclmul.multiply true fieldBinaryFieldInst i7 t21
        let i8 ←
          backend.x86_pclmul.multiply false fieldBinaryFieldInst t63 t63
        ok (some i8)

/-- [bulksketch::backend::x86_pclmul::{impl bulksketch::backend::contract::Arithmetic<F> for bulksketch::backend::x86_pclmul::Pclmul}::inverse]:
    Source: 'src/backend/x86_pclmul.rs', lines 50:4-57:5 -/
def backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic.inverse
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F) (a : Std.U64) :
  Result (Option Std.U64)
  := do
  backend.x86_pclmul.inverse fieldBinaryFieldInst a

/-- [bulksketch::backend::x86_pclmul::solve_quadratic]:
    Source: 'src/backend/x86_pclmul.rs', lines 298:0-307:1 -/
def backend.x86_pclmul.solve_quadratic
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F) (a : Std.U64) :
  Result (Option Std.U64)
  := do
  let i ← field.maps.trace fieldBinaryFieldInst a
  if i != 0#u8
  then ok none
  else
    let solution ← field.maps.quadratic_value fieldBinaryFieldInst a
    let square ←
      backend.x86_pclmul.multiply false fieldBinaryFieldInst solution solution
    let left_val ← lift (square ^^^ solution)
    if left_val = a
    then ok (some solution)
    else
      let _ ← core.fmt.Arguments.from_str (toStr "quadratic-map invariant")
      fail panic

/-- [bulksketch::backend::x86_pclmul::{impl bulksketch::backend::contract::Arithmetic<F> for bulksketch::backend::x86_pclmul::Pclmul}::solve_quadratic]:
    Source: 'src/backend/x86_pclmul.rs', lines 63:4-66:5 -/
def
  backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic.solve_quadratic
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F) (a : Std.U64) :
  Result (Option Std.U64)
  := do
  backend.x86_pclmul.solve_quadratic fieldBinaryFieldInst a

end bulksketch
