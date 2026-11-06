-- Exact declaration projection from the reviewed original-source extraction.
-- Only imports/type sharing are adapted; declarations below remain verbatim.
module
public import Arithmetic.InverseUsingTypes
public import Arithmetic.InverseGenerated
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

/-- [bulksketch::field::gf64::{impl core::ops::function::Fn<(u64, u64), u64> for bulksketch::field::gf64::mul<F>[TraitClause0]}::call]:
    Source: 'src/field/gf64.rs', lines 59:0-61:1 -/
def P.Insts.CoreOpsFunctionFnPairU64U64U64.call
  {F : Type _} (BinaryFieldInst : field.BinaryField F)
  (state : Std.U64 → Std.U64 → Result Std.U64)
  (args : (Std.U64 × Std.U64)) :
  Result Std.U64
  := do
  let (i, i1) := args
  field.gf64.mul BinaryFieldInst i i1

/-- [bulksketch::field::gf64::{impl core::ops::function::FnMut<(u64, u64), u64> for bulksketch::field::gf64::mul<F>[TraitClause0]}::call_mut]:
    Source: 'src/field/gf64.rs', lines 59:0-61:1 -/
def P.Insts.CoreOpsFunctionFnMutPairU64U64U64.call_mut
  {F : Type _} (BinaryFieldInst : field.BinaryField F)
  (state : Std.U64 → Std.U64 → Result Std.U64)
  (args : (Std.U64 × Std.U64)) :
  Result (Std.U64 × (Std.U64 → Std.U64 → Result Std.U64))
  := do
  let (i, i1) := args
  let i2 ← field.gf64.mul BinaryFieldInst i i1
  ok (i2, state)

/-- [bulksketch::field::gf64::{impl core::ops::function::FnOnce<(u64, u64), u64> for bulksketch::field::gf64::mul<F>[TraitClause0]}::call_once]:
    Source: 'src/field/gf64.rs', lines 59:0-61:1 -/
def P.Insts.CoreOpsFunctionFnOncePairU64U64U64.call_once
  {F : Type _} (BinaryFieldInst : field.BinaryField F)
  (state : Std.U64 → Std.U64 → Result Std.U64)
  (args : (Std.U64 × Std.U64)) :
  Result Std.U64
  := do
  let (i, i1) := args
  field.gf64.mul BinaryFieldInst i i1

/-- Trait implementation: [bulksketch::field::gf64::{impl core::ops::function::FnOnce<(u64, u64), u64> for bulksketch::field::gf64::mul<F>[TraitClause0]}]
    Source: 'src/field/gf64.rs', lines 59:0-61:1 -/
@[reducible]
def P.Insts.CoreOpsFunctionFnOncePairU64U64U64 {F : Type _} (BinaryFieldInst :
  field.BinaryField F) : core.ops.function.FnOnce (Std.U64 → Std.U64 →
  Result Std.U64) (Std.U64 × Std.U64) Std.U64 := {
  call_once := P.Insts.CoreOpsFunctionFnOncePairU64U64U64.call_once
    BinaryFieldInst
}

/-- Trait implementation: [bulksketch::field::gf64::{impl core::ops::function::FnMut<(u64, u64), u64> for bulksketch::field::gf64::mul<F>[TraitClause0]}]
    Source: 'src/field/gf64.rs', lines 59:0-61:1 -/
@[reducible]
def P.Insts.CoreOpsFunctionFnMutPairU64U64U64 {F : Type _} (BinaryFieldInst :
  field.BinaryField F) : core.ops.function.FnMut (Std.U64 → Std.U64 →
  Result Std.U64) (Std.U64 × Std.U64) Std.U64 := {
  FnOnceInst := P.Insts.CoreOpsFunctionFnOncePairU64U64U64 BinaryFieldInst
  call_mut := P.Insts.CoreOpsFunctionFnMutPairU64U64U64.call_mut
    BinaryFieldInst
}

/-- Trait implementation: [bulksketch::field::gf64::{impl core::ops::function::Fn<(u64, u64), u64> for bulksketch::field::gf64::mul<F>[TraitClause0]}]
    Source: 'src/field/gf64.rs', lines 59:0-61:1 -/
@[reducible]
def P.Insts.CoreOpsFunctionFnPairU64U64U64 {F : Type _} (BinaryFieldInst :
  field.BinaryField F) : core.ops.function.Fn (Std.U64 → Std.U64 → Result
  Std.U64) (Std.U64 × Std.U64) Std.U64 := {
  FnMutInst := P.Insts.CoreOpsFunctionFnMutPairU64U64U64 BinaryFieldInst
  call := P.Insts.CoreOpsFunctionFnPairU64U64U64.call BinaryFieldInst
}

/-- [bulksketch::field::gf64::{impl core::ops::function::Fn<(u64,), u64> for bulksketch::field::gf64::square<F>[TraitClause0]}::call]:
    Source: 'src/field/gf64.rs', lines 73:0-79:1 -/
def P.Insts.CoreOpsFunctionFnTupleU64U64.call
  {F : Type _} (BinaryFieldInst : field.BinaryField F)
  (state : Std.U64 → Result Std.U64) (args : Std.U64) :
  Result Std.U64
  := do
  field.gf64.square BinaryFieldInst args

/-- [bulksketch::field::gf64::{impl core::ops::function::FnMut<(u64,), u64> for bulksketch::field::gf64::square<F>[TraitClause0]}::call_mut]:
    Source: 'src/field/gf64.rs', lines 73:0-79:1 -/
def P.Insts.CoreOpsFunctionFnMutTupleU64U64.call_mut
  {F : Type _} (BinaryFieldInst : field.BinaryField F)
  (state : Std.U64 → Result Std.U64) (args : Std.U64) :
  Result (Std.U64 × (Std.U64 → Result Std.U64))
  := do
  let i ← field.gf64.square BinaryFieldInst args
  ok (i, state)

/-- [bulksketch::field::gf64::{impl core::ops::function::FnOnce<(u64,), u64> for bulksketch::field::gf64::square<F>[TraitClause0]}::call_once]:
    Source: 'src/field/gf64.rs', lines 73:0-79:1 -/
def P.Insts.CoreOpsFunctionFnOnceTupleU64U64.call_once
  {F : Type _} (BinaryFieldInst : field.BinaryField F)
  (state : Std.U64 → Result Std.U64) (args : Std.U64) :
  Result Std.U64
  := do
  field.gf64.square BinaryFieldInst args

/-- Trait implementation: [bulksketch::field::gf64::{impl core::ops::function::FnOnce<(u64,), u64> for bulksketch::field::gf64::square<F>[TraitClause0]}]
    Source: 'src/field/gf64.rs', lines 73:0-79:1 -/
@[reducible]
def P.Insts.CoreOpsFunctionFnOnceTupleU64U64 {F : Type _} (BinaryFieldInst :
  field.BinaryField F) : core.ops.function.FnOnce (Std.U64 → Result Std.U64)
  Std.U64 Std.U64 := {
  call_once := P.Insts.CoreOpsFunctionFnOnceTupleU64U64.call_once
    BinaryFieldInst
}

/-- Trait implementation: [bulksketch::field::gf64::{impl core::ops::function::FnMut<(u64,), u64> for bulksketch::field::gf64::square<F>[TraitClause0]}]
    Source: 'src/field/gf64.rs', lines 73:0-79:1 -/
@[reducible]
def P.Insts.CoreOpsFunctionFnMutTupleU64U64 {F : Type _} (BinaryFieldInst :
  field.BinaryField F) : core.ops.function.FnMut (Std.U64 → Result Std.U64)
  Std.U64 Std.U64 := {
  FnOnceInst := P.Insts.CoreOpsFunctionFnOnceTupleU64U64 BinaryFieldInst
  call_mut := P.Insts.CoreOpsFunctionFnMutTupleU64U64.call_mut BinaryFieldInst
}

/-- Trait implementation: [bulksketch::field::gf64::{impl core::ops::function::Fn<(u64,), u64> for bulksketch::field::gf64::square<F>[TraitClause0]}]
    Source: 'src/field/gf64.rs', lines 73:0-79:1 -/
@[reducible]
def P.Insts.CoreOpsFunctionFnTupleU64U64 {F : Type _} (BinaryFieldInst :
  field.BinaryField F) : core.ops.function.Fn (Std.U64 → Result Std.U64)
  Std.U64 Std.U64 := {
  FnMutInst := P.Insts.CoreOpsFunctionFnMutTupleU64U64 BinaryFieldInst
  call := P.Insts.CoreOpsFunctionFnTupleU64U64.call BinaryFieldInst
}

/-- [bulksketch::field::maps::inverse_using::{impl core::ops::function::Fn<(u64, u32), u64> for bulksketch::field::maps::inverse_using::{closure}<'_0, F, T1, T2>}::call]: loop body 0:
    Source: 'src/field/maps.rs', lines 43:8-45:9 -/
@[rust_loop_body]
def
  field.maps.inverse_using.closure.Insts.CoreOpsFunctionFnPairU64U32U64.call_loop.body
  {F : Type _} {T1 : Type _} {T2 : Type _} (coreopsfunctionFnT2TupleU64U64Inst
  : core.ops.function.Fn T2 Std.U64 Std.U64)
  (c : field.maps.inverse_using.closure F T1 T2)
  (iter : core.ops.range.Range Std.U32) (value : Std.U64) :
  Result (ControlFlow ((core.ops.range.Range Std.U32) × Std.U64) Std.U64)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
  match o with
  | none => ok (done value)
  | some _ =>
    let value1 ← coreopsfunctionFnT2TupleU64U64Inst.call c value
    ok (cont (iter1, value1))

/-- [bulksketch::field::maps::inverse_using::{impl core::ops::function::Fn<(u64, u32), u64> for bulksketch::field::maps::inverse_using::{closure}<'_0, F, T1, T2>}::call]: loop 0:
    Source: 'src/field/maps.rs', lines 43:8-45:9 -/
@[rust_loop]
def
  field.maps.inverse_using.closure.Insts.CoreOpsFunctionFnPairU64U32U64.call_loop
  {F : Type _} {T1 : Type _} {T2 : Type _} (coreopsfunctionFnT2TupleU64U64Inst
  : core.ops.function.Fn T2 Std.U64 Std.U64)
  (c : field.maps.inverse_using.closure F T1 T2)
  (iter : core.ops.range.Range Std.U32) (value : Std.U64) :
  Result Std.U64
  := do
  loop
    (fun (iter1, value1) =>
      field.maps.inverse_using.closure.Insts.CoreOpsFunctionFnPairU64U32U64.call_loop.body
      coreopsfunctionFnT2TupleU64U64Inst c iter1 value1)
    (iter, value)

/-- [bulksketch::field::maps::inverse_using::{impl core::ops::function::Fn<(u64, u32), u64> for bulksketch::field::maps::inverse_using::{closure}<'_0, F, T1, T2>}::call]:
    Source: 'src/field/maps.rs', lines 42:40-47:5 -/
def field.maps.inverse_using.closure.Insts.CoreOpsFunctionFnPairU64U32U64.call
  {F : Type _} {T1 : Type _} {T2 : Type _} (BinaryFieldInst : field.BinaryField
  F) (coreopsfunctionFnT1PairU64U64U64Inst : core.ops.function.Fn T1 (Std.U64
  × Std.U64) Std.U64) (coreopsfunctionFnT2TupleU64U64Inst :
  core.ops.function.Fn T2 Std.U64 Std.U64)
  (c : field.maps.inverse_using.closure F T1 T2)
  (tupled_args : (Std.U64 × Std.U32)) :
  Result Std.U64
  := do
  let (value, power) := tupled_args
  field.maps.inverse_using.closure.Insts.CoreOpsFunctionFnPairU64U32U64.call_loop
    coreopsfunctionFnT2TupleU64U64Inst c { start := 0#u32, «end» := power }
    value

/-- [bulksketch::field::maps::inverse_using::{impl core::ops::function::FnMut<(u64, u32), u64> for bulksketch::field::maps::inverse_using::{closure}<'_0, F, T1, T2>}::call_mut]:
    Source: 'src/field/maps.rs', lines 42:40-47:5 -/
def
  field.maps.inverse_using.closure.Insts.CoreOpsFunctionFnMutPairU64U32U64.call_mut
  {F : Type _} {T1 : Type _} {T2 : Type _} (BinaryFieldInst : field.BinaryField
  F) (coreopsfunctionFnT1PairU64U64U64Inst : core.ops.function.Fn T1 (Std.U64
  × Std.U64) Std.U64) (coreopsfunctionFnT2TupleU64U64Inst :
  core.ops.function.Fn T2 Std.U64 Std.U64)
  (state : field.maps.inverse_using.closure F T1 T2)
  (args : (Std.U64 × Std.U32)) :
  Result (Std.U64 × (field.maps.inverse_using.closure F T1 T2))
  := do
  let i ←
    field.maps.inverse_using.closure.Insts.CoreOpsFunctionFnPairU64U32U64.call
      BinaryFieldInst coreopsfunctionFnT1PairU64U64U64Inst
      coreopsfunctionFnT2TupleU64U64Inst state args
  ok (i, state)

/-- [bulksketch::field::maps::inverse_using::{impl core::ops::function::FnOnce<(u64, u32), u64> for bulksketch::field::maps::inverse_using::{closure}<'_0, F, T1, T2>}::call_once]:
    Source: 'src/field/maps.rs', lines 42:40-47:5 -/
def
  field.maps.inverse_using.closure.Insts.CoreOpsFunctionFnOncePairU64U32U64.call_once
  {F : Type _} {T1 : Type _} {T2 : Type _} (BinaryFieldInst : field.BinaryField
  F) (coreopsfunctionFnT1PairU64U64U64Inst : core.ops.function.Fn T1 (Std.U64
  × Std.U64) Std.U64) (coreopsfunctionFnT2TupleU64U64Inst :
  core.ops.function.Fn T2 Std.U64 Std.U64)
  (c : field.maps.inverse_using.closure F T1 T2) (p : (Std.U64 × Std.U32)) :
  Result Std.U64
  := do
  let (i, _) ←
    field.maps.inverse_using.closure.Insts.CoreOpsFunctionFnMutPairU64U32U64.call_mut
      BinaryFieldInst coreopsfunctionFnT1PairU64U64U64Inst
      coreopsfunctionFnT2TupleU64U64Inst c p
  ok i

/-- Trait implementation: [bulksketch::field::maps::inverse_using::{impl core::ops::function::FnOnce<(u64, u32), u64> for bulksketch::field::maps::inverse_using::{closure}<'_0, F, T1, T2>}]
    Source: 'src/field/maps.rs', lines 42:40-47:5 -/
@[reducible]
def field.maps.inverse_using.closure.Insts.CoreOpsFunctionFnOncePairU64U32U64
  {F : Type _} {T1 : Type _} {T2 : Type _} (BinaryFieldInst : field.BinaryField
  F) (coreopsfunctionFnT1PairU64U64U64Inst : core.ops.function.Fn T1 (Std.U64
  × Std.U64) Std.U64) (coreopsfunctionFnT2TupleU64U64Inst :
  core.ops.function.Fn T2 Std.U64 Std.U64) : core.ops.function.FnOnce
  (field.maps.inverse_using.closure F T1 T2) (Std.U64 × Std.U32) Std.U64 := {
  call_once :=
    field.maps.inverse_using.closure.Insts.CoreOpsFunctionFnOncePairU64U32U64.call_once
    BinaryFieldInst coreopsfunctionFnT1PairU64U64U64Inst
    coreopsfunctionFnT2TupleU64U64Inst
}

/-- Trait implementation: [bulksketch::field::maps::inverse_using::{impl core::ops::function::FnMut<(u64, u32), u64> for bulksketch::field::maps::inverse_using::{closure}<'_0, F, T1, T2>}]
    Source: 'src/field/maps.rs', lines 42:40-47:5 -/
@[reducible]
def field.maps.inverse_using.closure.Insts.CoreOpsFunctionFnMutPairU64U32U64 {F
  : Type _} {T1 : Type _} {T2 : Type _} (BinaryFieldInst : field.BinaryField F)
  (coreopsfunctionFnT1PairU64U64U64Inst : core.ops.function.Fn T1 (Std.U64 ×
  Std.U64) Std.U64) (coreopsfunctionFnT2TupleU64U64Inst : core.ops.function.Fn
  T2 Std.U64 Std.U64) : core.ops.function.FnMut
  (field.maps.inverse_using.closure F T1 T2) (Std.U64 × Std.U32) Std.U64 := {
  FnOnceInst :=
    field.maps.inverse_using.closure.Insts.CoreOpsFunctionFnOncePairU64U32U64
    BinaryFieldInst coreopsfunctionFnT1PairU64U64U64Inst
    coreopsfunctionFnT2TupleU64U64Inst
  call_mut :=
    field.maps.inverse_using.closure.Insts.CoreOpsFunctionFnMutPairU64U32U64.call_mut
    BinaryFieldInst coreopsfunctionFnT1PairU64U64U64Inst
    coreopsfunctionFnT2TupleU64U64Inst
}

/-- Trait implementation: [bulksketch::field::maps::inverse_using::{impl core::ops::function::Fn<(u64, u32), u64> for bulksketch::field::maps::inverse_using::{closure}<'_0, F, T1, T2>}]
    Source: 'src/field/maps.rs', lines 42:40-47:5 -/
@[reducible]
def field.maps.inverse_using.closure.Insts.CoreOpsFunctionFnPairU64U32U64 {F :
  Type _} {T1 : Type _} {T2 : Type _} (BinaryFieldInst : field.BinaryField F)
  (coreopsfunctionFnT1PairU64U64U64Inst : core.ops.function.Fn T1 (Std.U64 ×
  Std.U64) Std.U64) (coreopsfunctionFnT2TupleU64U64Inst : core.ops.function.Fn
  T2 Std.U64 Std.U64) : core.ops.function.Fn (field.maps.inverse_using.closure
  F T1 T2) (Std.U64 × Std.U32) Std.U64 := {
  FnMutInst :=
    field.maps.inverse_using.closure.Insts.CoreOpsFunctionFnMutPairU64U32U64
    BinaryFieldInst coreopsfunctionFnT1PairU64U64U64Inst
    coreopsfunctionFnT2TupleU64U64Inst
  call :=
    field.maps.inverse_using.closure.Insts.CoreOpsFunctionFnPairU64U32U64.call
    BinaryFieldInst coreopsfunctionFnT1PairU64U64U64Inst
    coreopsfunctionFnT2TupleU64U64Inst
}

/-- [bulksketch::field::maps::inverse_using]:
    Source: 'src/field/maps.rs', lines 37:0-48:1 -/
def field.maps.inverse_using
  {F : Type _} {T1 : Type _} {T2 : Type _} (BinaryFieldInst : field.BinaryField
  F) (coreopsfunctionFnT1PairU64U64U64Inst : core.ops.function.Fn T1 (Std.U64
  × Std.U64) Std.U64) (coreopsfunctionFnT2TupleU64U64Inst :
  core.ops.function.Fn T2 Std.U64 Std.U64) (a : Std.U64) (mul : T1)
  (square : T2) :
  Result (Option Std.U64)
  := do
  field.maps.inverse_with_frobenius BinaryFieldInst
    coreopsfunctionFnT1PairU64U64U64Inst
    (field.maps.inverse_using.closure.Insts.CoreOpsFunctionFnPairU64U32U64
    BinaryFieldInst coreopsfunctionFnT1PairU64U64U64Inst
    coreopsfunctionFnT2TupleU64U64Inst) a mul square

/-- [bulksketch::field::maps::inverse]:
    Source: 'src/field/maps.rs', lines 32:0-34:1 -/
def field.maps.inverse
  {F : Type _} (BinaryFieldInst : field.BinaryField F) (a : Std.U64) :
  Result (Option Std.U64)
  := do
  field.maps.inverse_using BinaryFieldInst
    (P.Insts.CoreOpsFunctionFnPairU64U64U64 BinaryFieldInst)
    (P.Insts.CoreOpsFunctionFnTupleU64U64 BinaryFieldInst) a (field.gf64.mul
    BinaryFieldInst) (field.gf64.square BinaryFieldInst)

end bulksketch
