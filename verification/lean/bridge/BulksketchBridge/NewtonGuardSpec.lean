import BulksketchBridge.NewtonGuardResidualSpec
import BulksketchBridge.RebuiltLfsrSpec

namespace BulksketchBridge.NewtonGuard

open Aeneas.Std bulksketch.backend.contract
open NewtonGuardResidual

abbrev mulWord := Inverse.multiplyNativeWord
abbrev squareWord := Square.expectedWord
abbrev fieldDictionary := bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField

/-- Five ascending cleared words and the denominator, in source order. -/
def clearedWords (odd : Slice U64) (degree : Nat) : Array U64 5#usize × U64 :=
  let s := odd[0]!
  let s2 := squareWord s
  let s4 := squareWord s2
  let a := odd[1]! ^^^ mulWord s s2
  let b := odd[2]! ^^^ mulWord odd[1]! s2
  if degree = 3 then
    (Array.make 5#usize [squareWord a ^^^ mulWord s b, b, mulWord s a, a, 0#u64], a)
  else
    let d := odd[2]! ^^^ mulWord s s4
    let c := odd[3]! ^^^ mulWord s (squareWord odd[1]!) ^^^ mulWord a s4
    let denominator := mulWord a odd[1]! ^^^ mulWord s d
    let u2 := mulWord b odd[1]! ^^^ mulWord s c
    (Array.make 5#usize [mulWord a c ^^^ mulWord b d, mulWord a denominator ^^^ mulWord s u2,
      u2, mulWord s denominator, denominator], denominator)

def clearedFrame (scratch : Slice U64) (words : Array U64 5#usize × U64) : Slice U64 :=
  (RebuiltLfsr.restorePrefix scratch words.1.to_slice).setAtNat 5 words.2

structure Admitted (odd : Slice U64) (degree : Usize) (scratch : Slice U64) : Prop where
  degreeCases : degree = 3#usize ∨ degree = 4#usize
  inputRoom : degree.val ≤ odd.length
  scratchRoom : (clearedWords odd degree.val).2 ≠ 0#u64 → 6 ≤ scratch.length

/-- The zero-denominator branch preserves scratch. The residual branch
returns the six cleared words and the original tail even on rejection. -/
def expected (odd : Slice U64) (degree : Usize) (scratch : Slice U64) : Bool × Slice U64 :=
  let words := clearedWords odd degree.val
  if words.2 = 0#u64 then (false, scratch)
  else
    let updated := clearedFrame scratch words
    (residualOK odd updated words.2 degree.val, updated)

def ActualNewtonGuardRefines : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (odd : Slice U64) (degree : Usize) (scratch : Slice U64),
    CorrectArithmetic kernels → Admitted odd degree scratch →
    bulksketch.decode.deg34.guard fieldDictionary kernels odd degree scratch =
      .ok (expected odd degree scratch)

end BulksketchBridge.NewtonGuard
