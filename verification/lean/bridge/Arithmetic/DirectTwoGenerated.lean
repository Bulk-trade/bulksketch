-- Exact original source declaration projection with scoped library bindings.
module
public import Arithmetic.SliceKernelTypes
public import Arithmetic.DirectTwoRuntime
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

local notation "core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any" =>
  DirectTwoRuntime.sharedAny

/-- [bulksketch::decode::direct::Pair]
    Source: 'src/decode/direct.rs', lines 6:0-10:1 -/
structure decode.direct.Pair where
  roots : Array Std.U64 2#usize

/-- [bulksketch::decode::direct::two::{closure}]
    Source: 'src/decode/direct.rs', lines 53:48-53:89 -/
@[reducible]
def decode.direct.two.closure (F : Type _) (K : Type _) := Unit

/-- [bulksketch::decode::direct::two::{impl core::ops::function::FnMut<(&'_0 u64,), bool> for bulksketch::decode::direct::two::{closure}<'_0, F, K>}::call_mut]:
    Source: 'src/decode/direct.rs', lines 53:48-53:89 -/
def
  decode.direct.two.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool.call_mut
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (c : decode.direct.two.closure F K) (tupled_args : Std.U64) :
  Result (Bool × (decode.direct.two.closure F K))
  := do
  if tupled_args = 0#u64
  then ok (true, ())
  else
    let i ← fieldBinaryFieldInst.MASK
    let i1 ← lift (~~~ i)
    let i2 ← lift (tupled_args &&& i1)
    ok (i2 != 0#u64, ())

/-- [bulksketch::decode::direct::two::{impl core::ops::function::FnOnce<(&'_0 u64,), bool> for bulksketch::decode::direct::two::{closure}<'_0, F, K>}::call_once]:
    Source: 'src/decode/direct.rs', lines 53:48-53:89 -/
def
  decode.direct.two.closure.Insts.CoreOpsFunctionFnOnceTupleShared0U64Bool.call_once
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (c : decode.direct.two.closure F K) (i : Std.U64) :
  Result Bool
  := do
  let (b, _) ←
    decode.direct.two.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool.call_mut
      fieldBinaryFieldInst backendcontractBulkKernelsInst () i
  ok b

/-- Trait implementation: [bulksketch::decode::direct::two::{impl core::ops::function::FnOnce<(&'_0 u64,), bool> for bulksketch::decode::direct::two::{closure}<'_0, F, K>}]
    Source: 'src/decode/direct.rs', lines 53:48-53:89 -/
@[reducible]
def decode.direct.two.closure.Insts.CoreOpsFunctionFnOnceTupleShared0U64Bool {F
  : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F) :
  core.ops.function.FnOnce (decode.direct.two.closure F K) Std.U64 Bool := {
  call_once :=
    decode.direct.two.closure.Insts.CoreOpsFunctionFnOnceTupleShared0U64Bool.call_once
    fieldBinaryFieldInst backendcontractBulkKernelsInst
}

/-- Trait implementation: [bulksketch::decode::direct::two::{impl core::ops::function::FnMut<(&'_0 u64,), bool> for bulksketch::decode::direct::two::{closure}<'_0, F, K>}]
    Source: 'src/decode/direct.rs', lines 53:48-53:89 -/
@[reducible]
def decode.direct.two.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool {F
  : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F) :
  core.ops.function.FnMut (decode.direct.two.closure F K) Std.U64 Bool := {
  FnOnceInst :=
    decode.direct.two.closure.Insts.CoreOpsFunctionFnOnceTupleShared0U64Bool
    fieldBinaryFieldInst backendcontractBulkKernelsInst
  call_mut :=
    decode.direct.two.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool.call_mut
    fieldBinaryFieldInst backendcontractBulkKernelsInst
}

/-- [bulksketch::decode::direct::two]:
    Source: 'src/decode/direct.rs', lines 22:0-61:1 -/
def decode.direct.two
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (s : Std.U64) (syndrome3 : Std.U64) :
  Result (Option decode.direct.Pair)
  := do
  let o ← backendcontractBulkKernelsInst.ArithmeticInst.inverse s
  let inverse ← core.option.Option.expect o (toStr "eligible nonzero S1")
  let square ← backendcontractBulkKernelsInst.ArithmeticInst.square s
  let cube ← backendcontractBulkKernelsInst.ArithmeticInst.mul square s
  let i ← lift (syndrome3 ^^^ cube)
  let product ← backendcontractBulkKernelsInst.ArithmeticInst.mul i inverse
  if product = 0#u64
  then ok none
  else
    let i1 ← backendcontractBulkKernelsInst.ArithmeticInst.square inverse
    let target ← backendcontractBulkKernelsInst.ArithmeticInst.mul product i1
    let o1 ←
      backendcontractBulkKernelsInst.ArithmeticInst.solve_quadratic target
    let cf ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o1
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let i2 ← fieldBinaryFieldInst.MASK
      let i3 ← lift (~~~ i2)
      let i4 ← lift (val &&& i3)
      if i4 != 0#u64
      then ok none
      else
        let i5 ← backendcontractBulkKernelsInst.ArithmeticInst.square val
        let i6 ← lift (i5 ^^^ val)
        if i6 != target
        then ok none
        else
          let first ← backendcontractBulkKernelsInst.ArithmeticInst.mul s val
          let i7 ← lift (first ^^^ s)
          let i8 ←
            Array.index_usize (Array.make 2#usize [ first, i7 ]) 0#usize
          let i9 ←
            Array.index_usize (Array.make 2#usize [ first, i7 ]) 1#usize
          if i8 = i9
          then ok none
          else
            let s1 ← lift (Array.to_slice (Array.make 2#usize [ first, i7 ]))
            let i10 ← core.slice.Slice.iter s1
            let (b, _) ←
              core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any
                (decode.direct.two.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool
                fieldBinaryFieldInst backendcontractBulkKernelsInst) i10 ()
            if b
            then ok none
            else ok (some { roots := (Array.make 2#usize [ first, i7 ]) })
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual
        decode.direct.Pair residual

end bulksketch
