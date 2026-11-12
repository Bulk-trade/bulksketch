import BulksketchBridge.DenseMulConvolutionSpec
import BulksketchBridge.BmDiscrepancySpec
import BulksketchBridge.InverseFieldSpec
import BulksketchBridge.DenseReducerSquareSpec

namespace BulksketchBridge.DenseDivision

open Aeneas.Std DenseCoefficient RebuiltLfsr BmDiscrepancy
open DenseMulConvolutionSpec
open DenseMulReductionSpec (reduceWord)
open scoped BulksketchBridge.DenseMulReductionSpec

def initialRaw (input : Slice U64) (raw : Slice Raw) : Slice Raw :=
  raw.setSlice! 0 (input.val.map fun word => ⟨word, 0#u64⟩)

def factorWord (inverse : U64) (product : Raw) : U64 :=
  let reduced := reduceWord product
  if inverse = 1#u64 then reduced else Inverse.multiplyNativeWord reduced inverse

def updateWord (divisor : Slice U64) (factor : U64) (offset top slot : Nat) (original : Raw) : Raw :=
  if offset ≤ slot ∧ slot < top then
    let word := divisor[slot - offset]!
    if factor = 0#u64 then original
    else if factor = 1#u64 then {original with lo := original.lo ^^^ word}
    else xorProduct original (RawMul.expectedProduct factor word)
  else original

/-- Each pass writes its quotient coefficient, updates only the lower
divisor window, and retains the eliminated raw slot in memory. -/
def updateRaw (divisor : Slice U64) (factor : U64) (offset top : Nat) (raw : Slice Raw) : Slice Raw :=
  Slice.from (List.ofFn fun slot : Fin raw.length =>
    updateWord divisor factor offset top slot.val raw[slot.val]!) (by simp)

def descend (divisor : Slice U64) (degree : Nat) (inverse : U64) :
    Nat → Slice U64 → Slice Raw → Slice U64 × Slice Raw
  | 0, quotient, raw => (quotient, raw)
  | count + 1, quotient, raw =>
    let top := degree + count
    let factor := factorWord inverse raw[top]!
    descend divisor degree inverse count (quotient.setAtNat count factor)
      (updateRaw divisor factor count top raw)

def remainderWords (raw : Slice Raw) (count : Nat) : Slice U64 :=
  Slice.from (List.ofFn fun index : Fin (min count raw.length) =>
    reduceWord raw[index.val]!) (by
      simp only [List.length_ofFn]
      exact (Nat.min_le_right _ _).trans raw.length_ineq)

def cleared (words : Slice U64) (count : Nat) : Slice U64 :=
  restorePrefix words (zeroWords (prefixSlice words count))

/-- Complete scalar division schedule, with caller scratch outside the
written prefixes retained and eliminated raw top slots left in memory. -/
def expectedDivRem (a b q rem : Slice U64) (raw : Slice Raw) (inverse : U64) :
    (Usize × Usize) × Slice U64 × Slice U64 × Slice Raw :=
  let size := a.length + 1
  let degree := b.length - 1
  let remCount := min degree a.length
  let (quotient, scratch) :=
    descend b degree inverse (a.length - degree) (cleared q size) (initialRaw a raw)
  let remainder := restorePrefix (cleared rem size) (remainderWords scratch remCount)
  ((DenseReducerSquare.outputLength quotient size, DenseReducerSquare.outputLength remainder remCount),
    quotient, remainder, scratch)

end BulksketchBridge.DenseDivision
