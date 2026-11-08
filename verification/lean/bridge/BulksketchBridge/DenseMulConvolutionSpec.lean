import Arithmetic.DenseMulConvolutionGenerated
import BulksketchBridge.DenseMulReductionSpec
import BulksketchBridge.RawMulSpec

namespace BulksketchBridge.DenseMulConvolutionSpec

open Aeneas Aeneas.Std BulksketchBridge.MutableZip
open bulksketch
open scoped BulksketchBridge.DenseMulReductionSpec

abbrev dictionary := DenseMulReductionSpec.dictionary

def xorProduct (left right : types.RawProduct) : types.RawProduct :=
  ⟨left.lo ^^^ right.lo, left.hi ^^^ right.hi⟩

def rowWord (left : U64) (b : Slice U64) (old : types.RawProduct)
    (offset slot : Nat) : types.RawProduct :=
  if offset ≤ slot ∧ slot < offset + b.length then
    xorProduct old (RawMul.expectedProduct left b[slot - offset]!)
  else old

/-- Accumulate one shifted product row while preserving the whole scratch frame. -/
def row (left : U64) (b : Slice U64) (raw : Slice types.RawProduct)
    (offset : Nat) : Slice types.RawProduct :=
  Slice.from (List.ofFn fun slot : Fin raw.length =>
    rowWord left b raw[slot.val]! offset slot.val) (by simp)

@[simp] theorem row_length (left : U64) (b : Slice U64) (raw : Slice types.RawProduct)
    (offset : Nat) : (row left b raw offset).length = raw.length := by
  simp [row]

theorem row_word (left : U64) (b : Slice U64) (raw : Slice types.RawProduct)
    (offset slot : Nat) (bounded : slot < raw.length) :
    (row left b raw offset)[slot]! = rowWord left b raw[slot]! offset slot := by
  simp only [row, Slice.getElem!_Nat_eq, Slice.from_val]
  rw [← List.Inhabited_getElem_eq_getElem! _ slot (by simpa using bounded), List.getElem_ofFn]

/-- The next `count` rows, starting at the enumeration index `start`. -/
def accumulateRows (a b : Slice U64) (raw : Slice types.RawProduct)
    (start : Nat) : Nat → Slice types.RawProduct
  | 0 => raw
  | count + 1 => accumulateRows a b (row a[start]! b raw start) (start + 1) count

@[simp] theorem accumulate_length (a b : Slice U64) (raw : Slice types.RawProduct)
    (start count : Nat) : (accumulateRows a b raw start count).length = raw.length := by
  induction count generalizing raw start with
  | zero => rfl
  | succ count ih => simp only [accumulateRows, ih, row_length]

theorem accumulate_word (a b : Slice U64) (raw : Slice types.RawProduct)
    (start count slot : Nat) (bounded : slot < raw.length) :
    (accumulateRows a b raw start count)[slot]! =
      (List.range' start count).foldl (fun old index => rowWord a[index]! b old index slot) raw[slot]! := by
  induction count generalizing raw start with
  | zero => rfl
  | succ count ih =>
    rw [accumulateRows, ih _ _ (by simpa using bounded), row_word _ _ _ _ _ bounded]
    rfl

/-- The row pass leaves the prefix before its first row and the tail past its
last shifted window intact. -/
theorem accumulate_frame (a b : Slice U64) (raw : Slice types.RawProduct)
    (start count slot : Nat) (bounded : slot < raw.length)
    (outside : slot < start ∨ start + count + b.length ≤ slot + 1) :
    (accumulateRows a b raw start count)[slot]! = raw[slot]! := by
  induction count generalizing raw start with
  | zero => rfl
  | succ count ih =>
    rw [accumulateRows, ih _ _ (by simpa using bounded) (by omega), row_word _ _ _ _ _ bounded]
    unfold rowWord
    rw [ite_eq_right (by omega)]

def iteratorAt (a : Slice U64) (count : Usize) :
    core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter U64) :=
  ⟨⟨a, count.val⟩, count⟩

def RawMulAgrees {K : Type} (kernels : backend.contract.BulkKernels K field.Gf64) : Prop :=
  ∀ left right, kernels.ArithmeticInst.raw_mul left right = field.gf64.raw_mul dictionary left right

def innerLoopFrame : Prop :=
  ∀ {K : Type} (kernels : backend.contract.BulkKernels K field.Gf64), RawMulAgrees kernels →
    ∀ (left : U64) (window : Slice types.RawProduct) (b : Slice U64), window.length = b.length →
    ∀ start : Nat, start ≤ window.length →
    ∀ back : State types.RawProduct U64 → State types.RawProduct U64,
      ∃ restore : State types.RawProduct U64 → State types.RawProduct U64,
        poly.Dense.Insts.BulksketchPolyPolynomial.mul_into_loop0_loop0 dictionary kernels
          (stateAt window b start) back left = Result.ok (stateAt window b window.length, restore) ∧
        restore (stateAt window b window.length) = back (stateAt
          (mapFrom window b (fun old right => xorProduct old (RawMul.expectedProduct left right)) start)
          b window.length)

def outerLoopFrame : Prop :=
  ∀ {K : Type} (kernels : backend.contract.BulkKernels K field.Gf64), RawMulAgrees kernels →
    ∀ (a b : Slice U64) (raw : Slice types.RawProduct) (count : Usize),
      count.val ≤ a.length → a.length + b.length ≤ raw.length →
      poly.Dense.Insts.BulksketchPolyPolynomial.mul_into_loop0 dictionary kernels
        (iteratorAt a count) b raw =
        Result.ok (accumulateRows a b raw count.val (a.length - count.val))

end BulksketchBridge.DenseMulConvolutionSpec
