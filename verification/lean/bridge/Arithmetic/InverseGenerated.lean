-- Exact declaration projection from the successful original-source Aeneas output.
-- Original output remains unchanged under extraction/inverse-chain/Inverse/.
-- Only the import/type reuse boundary is adapted; all three source declaration
-- texts below are byte-identical to that output. Existing Gf64 declarations are
-- reused from Arithmetic.Funs to avoid duplicate global declarations.
module
public import Arithmetic.Funs
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

/-- [bulksketch::field::maps::inverse_with_frobenius]: loop body 0:
    Source: 'src/field/maps.rs', lines 66:4-73:5 -/
@[rust_loop_body]
def field.maps.inverse_with_frobenius_loop.body
  {T1 : Type _} {T2 : Type _} (coreopsfunctionFnT1PairU64U64U64Inst :
  core.ops.function.Fn T1 (Std.U64 × Std.U64) Std.U64)
  (coreopsfunctionFnT2PairU64U32U64Inst : core.ops.function.Fn T2 (Std.U64 ×
  Std.U32) Std.U64) (a : Std.U64) (mul : T1) (frobenius : T2)
  (target : Std.U32)
  (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.U32))
  (k : Std.U32) (t : Std.U64) :
  Result (ControlFlow ((core.iter.adapters.rev.Rev (core.ops.range.Range
    Std.U32)) × Std.U32 × Std.U64) Std.U64)
  := do
  let (o, iter1) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepU32)
      iter
  match o with
  | none => ok (done t)
  | some bit =>
    let i ← coreopsfunctionFnT2PairU64U32U64Inst.call frobenius (t, k)
    let t1 ← coreopsfunctionFnT1PairU64U64U64Inst.call mul (i, t)
    let k1 ← k * 2#u32
    let i1 ← 1#u32 <<< bit
    let i2 ← lift (target &&& i1)
    if i2 != 0#u32
    then
      let i3 ←
        coreopsfunctionFnT2PairU64U32U64Inst.call frobenius (t1, 1#u32)
      let t2 ← coreopsfunctionFnT1PairU64U64U64Inst.call mul (i3, a)
      let k2 ← k1 + 1#u32
      ok (cont (iter1, k2, t2))
    else ok (cont (iter1, k1, t1))

/-- [bulksketch::field::maps::inverse_with_frobenius]: loop 0:
    Source: 'src/field/maps.rs', lines 66:4-73:5 -/
@[rust_loop]
def field.maps.inverse_with_frobenius_loop
  {T1 : Type _} {T2 : Type _} (coreopsfunctionFnT1PairU64U64U64Inst :
  core.ops.function.Fn T1 (Std.U64 × Std.U64) Std.U64)
  (coreopsfunctionFnT2PairU64U32U64Inst : core.ops.function.Fn T2 (Std.U64 ×
  Std.U32) Std.U64)
  (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.U32))
  (a : Std.U64) (mul : T1) (frobenius : T2) (target : Std.U32) (k : Std.U32)
  (t : Std.U64) :
  Result Std.U64
  := do
  loop
    (fun (iter1, k1, t1) => field.maps.inverse_with_frobenius_loop.body
      coreopsfunctionFnT1PairU64U64U64Inst coreopsfunctionFnT2PairU64U32U64Inst
      a mul frobenius target iter1 k1 t1)
    (iter, k, t)

/-- [bulksketch::field::maps::inverse_with_frobenius]:
    Source: 'src/field/maps.rs', lines 51:0-75:1 -/
def field.maps.inverse_with_frobenius
  {F : Type _} {T1 : Type _} {T2 : Type _} (BinaryFieldInst : field.BinaryField
  F) (coreopsfunctionFnT1PairU64U64U64Inst : core.ops.function.Fn T1 (Std.U64
  × Std.U64) Std.U64) (coreopsfunctionFnT2PairU64U32U64Inst :
  core.ops.function.Fn T2 (Std.U64 × Std.U32) Std.U64) (a : Std.U64)
  (mul : T1) (frobenius : T2) :
  Result (Option Std.U64)
  := do
  let i ← BinaryFieldInst.MASK
  let i1 ← lift (~~~ i)
  let left_val ← lift (a &&& i1)
  if left_val = 0#u64
  then
    if a = 0#u64
    then ok none
    else
      if a = 1#u64
      then ok (some 1#u64)
      else
        let i2 ← BinaryFieldInst.BITS
        let target ← i2 - 1#u32
        let i3 ← lift (core.num.U32.leading_zeros target)
        let i4 ← core.num.U32.BITS - i3
        let i5 ← i4 - 1#u32
        let iter ←
          core.iter.traits.iterator.Iterator.rev.trait_default
            (core.iter.traits.iterator.IteratorRange core.iter.range.StepU32)
            (core.ops.range.Range.Insts.DoubleEndedIterator
            core.iter.range.StepU32) { start := 0#u32, «end» := i5 }
        let t ←
          field.maps.inverse_with_frobenius_loop
            coreopsfunctionFnT1PairU64U64U64Inst
            coreopsfunctionFnT2PairU64U32U64Inst iter a mul frobenius target
            1#u32 a
        let i6 ←
          coreopsfunctionFnT2PairU64U32U64Inst.call frobenius (t, 1#u32)
        ok (some i6)
  else
    let _ ← core.fmt.Arguments.from_str (toStr "noncanonical field operand")
    fail panic

end bulksketch
