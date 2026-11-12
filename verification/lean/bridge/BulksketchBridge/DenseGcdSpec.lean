import Arithmetic.DenseGcdGenerated
import BulksketchBridge.BmEntrySpec
import BulksketchBridge.BmTerminalSpec
import BulksketchBridge.TimesXModSpec
import BulksketchBridge.ClosedLeafWindows

namespace BulksketchBridge.DenseGcd

open Aeneas.Std DenseCoefficient RebuiltLfsr BmEntry
open bulksketch.backend.contract bulksketch.types

abbrev DivRem := DenseDivisionRuntime.DivRem
abbrev Back := Slice U64 → Slice U64 → Slice U64 → Slice U64 × Slice U64 × Slice U64
abbrev LoopResult := Slice RawProduct × Slice U64 × Slice U64 × Slice U64 × Slice U64 × Usize × Back
abbrev DivisionResult := (Usize × Usize) × Slice U64 × Slice U64 × Slice RawProduct
abbrev Output := Usize × Slice U64 × Slice U64 × Slice RawProduct
abbrev dictionary := BmTerminal.fieldDictionary

def Normal (words : Slice U64) : Prop :=
  0 < words.length → words[words.length - 1]! ≠ 0#u64

structure State where
  back : Back
  raw : Slice RawProduct
  left : Slice U64
  right : Slice U64
  quotient : Slice U64
  remainder : Slice U64
  leftLen : Usize
  rightLen : Usize

def State.finish (state : State) : LoopResult :=
  (state.raw, state.left, state.right, state.quotient, state.remainder, state.leftLen, state.back)

def State.leftWords (state : State) : Slice U64 := prefixSlice state.left state.leftLen.val
def State.rightWords (state : State) : Slice U64 := prefixSlice state.right state.rightLen.val

structure Ready (width : Nat) (state : State) : Prop where
  leftWidth : state.left.length = width
  rightWidth : state.right.length = width
  quotientWidth : state.quotient.length = width
  remainderWidth : state.remainder.length = width
  rawRoom : width ≤ state.raw.length
  leftRoom : state.leftLen.val < width
  rightRoom : state.rightLen.val < width
  leftNormal : Normal state.leftWords
  rightNormal : Normal state.rightWords

/-- Exact returned slice widths, strict Euclidean decrease, and a normalized
remainder are the call-specific division obligations of the original loop. -/
def DivisionLaw (division : DivRem) {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) : Prop :=
  ∀ (left right quotient remainder : Slice U64) (raw : Slice RawProduct),
    Normal left → Normal right → 0 < right.length →
    left.length + 1 ≤ quotient.length → left.length + 1 ≤ remainder.length →
    left.length + 1 ≤ raw.length →
    ∃ (qLen remLen : Usize) (qOut remOut : Slice U64) (rawOut : Slice RawProduct),
      division dictionary kernels left right quotient remainder raw = .ok ((qLen, remLen), qOut, remOut, rawOut) ∧
      qOut.length = quotient.length ∧ remOut.length = remainder.length ∧ rawOut.length = raw.length ∧
      remLen.val < right.length ∧ Normal (prefixSlice remOut remLen.val)

def State.advance (state : State) (result : DivisionResult) : State :=
  let ((_, remLen), quotient, remainder, raw) := result
  ⟨fun left right spare => state.back spare left right, raw, state.right, remainder,
    quotient, state.left, state.rightLen, remLen⟩

def run (division : DivRem) {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) :
    Nat → State → Result State
  | 0, state => if state.rightLen = 0#usize then .ok state else .fail .panic
  | fuel + 1, state =>
    if state.rightLen = 0#usize then .ok state else do
      let step ← division dictionary kernels state.leftWords state.rightWords state.quotient state.remainder state.raw
      run division kernels fuel (state.advance step)

def startState (width : Nat) (a b work : Slice U64) (raw : Slice RawProduct) : State :=
  let front := prefixSlice work (4 * width)
  let rest := tail front width
  let rest1 := tail rest width
  ⟨fun left right spare => (left, right, spare), raw,
    restorePrefix (prefixSlice front width) a, restorePrefix (prefixSlice rest width) b,
    prefixSlice rest1 width, tail rest1 width, Slice.len a, Slice.len b⟩

def restoreWork (work : Slice U64) (width : Nat) (state : State) : Slice U64 :=
  let front := prefixSlice work (4 * width)
  let rest := tail front width
  let rest1 := tail rest width
  let (left, right, spare) := state.back state.left state.right state.remainder
  restorePrefix work
    (splitBack front width (left, splitBack rest width (right, splitBack rest1 width (state.quotient, spare))))

noncomputable def scaledPrefix (words : Slice U64) (scale : U64) : Slice U64 :=
  Slice.from (words.val.map fun word => Inverse.multiplyNativeWord scale word) (by simpa using words.length_ineq)

noncomputable def gcdWords (state : State) : Slice U64 :=
  if state.leftLen = 0#usize then state.leftWords
  else
    let leading := state.left[state.leftLen.val - 1]!
    if leading = 1#u64 then state.leftWords
    else scaledPrefix state.leftWords (DirectTwo.inverseWord leading)

noncomputable def destination (dst : Slice U64) (limit : Nat) (state : State) : Slice U64 :=
  let zeroed := restorePrefix dst (zeroWords (prefixSlice dst limit))
  if state.leftLen = 0#usize then zeroed else restorePrefix zeroed (gcdWords state)

noncomputable def expected (division : DivRem) {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (a b dst work : Slice U64) (raw : Slice RawProduct) : Result Output := do
  let limit := max a.length b.length
  let width := limit + 1
  let state ← run division kernels b.length (startState width a b work raw)
  .ok (state.leftLen, destination dst limit state, restoreWork work width state, state.raw)

/-- The original wrapper agrees with the explicit finite rotation of
left, right, and remainder and preserves the original four-slot work frame. -/
def ActualMonicGcd : Prop :=
  ∀ (division : DivRem) {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (a b dst work : Slice U64) (raw : Slice RawProduct),
    DivisionLaw division kernels → BmTerminal.NativeInverse kernels → TimesXMod.ExactScaleXor kernels →
    Normal a → Normal b →
    max a.length b.length ≤ dst.length →
    4 * (max a.length b.length + 1) ≤ work.length →
    2 * (max a.length b.length + 1) ≤ raw.length →
    ∃ output,
      bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial.monic_gcd_into division dictionary kernels a b dst work raw =
        .ok output ∧ expected division kernels a b dst work raw = .ok output

end BulksketchBridge.DenseGcd
