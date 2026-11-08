import Arithmetic.RootDivideGenerated
import BulksketchBridge.BmEntrySpec
import BulksketchBridge.ClosedLeafAdvanceSpec
import BulksketchBridge.StageChargeSpec

namespace BulksketchBridge.RootDivide

open Aeneas.Std Aeneas.Std.RootDivideRuntime
open DenseCoefficient RebuiltLfsr BmEntry WorkSchedule
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types

abbrev Reply := core.result.Result (core.result.Result Stage DecodeFailure) DecodeError
abbrev Output := Reply × Roots × FactorWork × (FactorWork → FactorWork) × Slice U64 × Slice FactorFrame × WorkMeter

def unchanged (roots : Roots) (buffers : FactorWork) (factors : Slice U64) (stack : Slice FactorFrame)
    (meter : WorkMeter) (reply : Reply) : Output :=
  (reply, roots, buffers, id, factors, stack, meter)

def afterCall (roots : Roots) (buffers : FactorWork) (quotient remainder : Slice U64)
    (raw : Slice RawProduct) : FactorWork :=
  { buffers with work := splitBack buffers.work (roots.degree.val + 2) (quotient, remainder), raw := raw }

def reached (exactDivision : ExactDivide) {F K : Type}
    (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F)
    (roots : Roots) (buffers : FactorWork) (candidate : Option Usize) (quotient remainder : Slice U64)
    (raw : Slice RawProduct) : Prop :=
  exactDivision field kernels buffers.modulus (prefixSlice buffers.gcd roots.gcd_len.val)
    (prefixSlice buffers.work (roots.degree.val + 2)) (tail buffers.work (roots.degree.val + 2)) buffers.raw =
    .ok (candidate, quotient, remainder, raw)

/-- Checked prices in source evaluation order, including intermediate overflow. -/
def divideCost (degree : Usize) : CostResult :=
  match checkedCost (degree.val + 1) with
  | .Err error => .Err error
  | .Ok width => match checkedCost (width.val * width.val) with
    | .Err error => .Err error
    | .Ok square => match checkedCost (4 * square.val) with
      | .Err error => .Err error
      | .Ok work => checkedCost (work.val + 128)

def assemblyCost (degree : Usize) : CostResult :=
  match checkedCost (degree.val + 1) with
  | .Err error => .Err error
  | .Ok width => checkedCost (4 * width.val)

structure DivideReady (roots : Roots) (buffers : FactorWork) : Prop where
  workRoom : roots.degree.val + 2 ≤ buffers.work.length
  gcdRoom : roots.gcd_len.val ≤ buffers.gcd.length

/-- Bounds needed only after both charges and checked offsets succeed. -/
structure CommitReady (roots : Roots) (buffers : FactorWork) (factors : Slice U64)
    (stack : Slice FactorFrame) (quotient : Slice U64) (length start stop : Usize) : Prop where
  factorRoom : stop.val ≤ factors.length
  quotientRoom : length.val ≤ quotient.length
  slotRoom : roots.pending.val < stack.length
  modulusRoom : roots.gcd_len.val ≤ buffers.modulus.length
  directionRoom : roots.direction.val + 1 ≤ U32.max
  affineRank : roots.affine = true → 0 < roots.affine_rank.val ∧ roots.affine_rank.val ≤ 64
  affineBasis : roots.affine = true → ∃ basis, buffers.basis.directions = some basis
  affineBase : roots.affine = true → 0 < start.val + roots.stride.val ∧ start.val + roots.stride.val ≤ factors.length

def directionWord (roots : Roots) : U32 := ⟨BitVec.ofNat 32 (roots.direction.val + 1)⟩

/-- The pending child owns the copied quotient and optional affine base.
The active left modulus is replaced by the GCD, retaining other scratch. -/
def committed (roots : Roots) (buffers : FactorWork) (factors : Slice U64)
    (stack : Slice FactorFrame) (meter : WorkMeter)
    (length start : Usize) (quotient remainder : Slice U64) (raw : Slice RawProduct) : Output :=
  let direction := directionWord roots
  let rank := ClosedLeafAdvance.usizeWord (roots.affine_rank.val - 1)
  let next := { roots with
    pending := ClosedLeafAdvance.usizeWord (roots.pending.val + 1)
    degree := roots.gcd_degree
    direction := direction
    checked := true
    affine_rank := if roots.affine then rank else roots.affine_rank }
  let copied := factors.setSlice! start.val (prefixSlice quotient length.val).val
  let frame : FactorFrame := ⟨UScalar.cast .U64 start, UScalar.cast .U64 length, direction, 1#u32⟩
  let pushed := stack.set roots.pending frame
  let (finalFactors, finalStack) :=
    if roots.affine then
      let base := ClosedLeafAdvance.usizeWord (start.val + roots.stride.val - 1)
      let word := (buffers.basis.directions.map fun basis => basis[rank.val]!).getD 0#u64
      (copied.set base (roots.affine_base ^^^ word),
        pushed.set roots.pending {frame with next_direction := UScalar.cast .U32 rank})
    else (copied, pushed)
  let nextBuffers := { afterCall roots buffers quotient remainder raw with
    modulus := restorePrefix buffers.modulus (prefixSlice buffers.gcd roots.gcd_len.val) }
  (.Ok (.Ok (ClosedLeafAdvance.stageFor next)), next, nextBuffers, id, finalFactors, finalStack, meter)

def expected (exactDivision : ExactDivide) {F K : Type}
    (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F)
    (roots : Roots) (buffers : FactorWork) (factors : Slice U64)
    (stack : Slice FactorFrame) (meter : WorkMeter) : Result Output := do
  match StageCharge.chargeResult meter (divideCost roots.degree) with
  | (.Err error, paid) => .ok (unchanged roots buffers factors stack paid (.Err error))
  | (.Ok (), paid) =>
    let (candidate, quotient, remainder, raw) ← exactDivision field kernels buffers.modulus
      (prefixSlice buffers.gcd roots.gcd_len.val)
      (prefixSlice buffers.work (roots.degree.val + 2))
      (tail buffers.work (roots.degree.val + 2)) buffers.raw
    let postCall := afterCall roots buffers quotient remainder raw
    match candidate with
    | none => .ok (unchanged roots postCall factors stack paid (.Ok (.Err .InvalidLocator)))
    | some length =>
      match StageCharge.chargeResult paid (assemblyCost roots.degree) with
      | (.Err error, finalMeter) =>
        .ok (unchanged roots postCall factors stack finalMeter (.Err error))
      | (.Ok (), finalMeter) =>
        match Usize.checked_mul roots.pending roots.stride with
        | none => .ok (unchanged roots postCall factors stack finalMeter (.Err .ScratchTooSmall))
        | some start =>
          match Usize.checked_add start length with
          | none => .ok (unchanged roots postCall factors stack finalMeter (.Err .ScratchTooSmall))
          | some _ => .ok (committed roots buffers factors stack finalMeter length start quotient remainder raw)

/-- Complete source frame on all admitted branches. Arithmetic overflow in
either checked offset remains a modeled Rust result. -/
def ActualRootDivide : Prop :=
  ∀ (exactDivision : ExactDivide) {F K : Type}
    (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F)
    (roots : Roots) (buffers : FactorWork) (factors : Slice U64) (stack : Slice FactorFrame)
    (meter : WorkMeter),
    DivideReady roots buffers →
    (∃ candidate quotient remainder raw,
      reached exactDivision field kernels roots buffers candidate quotient remainder raw) →
    (∀ length quotient remainder raw start stop,
      reached exactDivision field kernels roots buffers (some length) quotient remainder raw →
      Usize.checked_mul roots.pending roots.stride = some start →
      Usize.checked_add start length = some stop →
      CommitReady roots buffers factors stack quotient length start stop) →
    Roots.divide exactDivision field kernels roots buffers factors stack meter =
      expected exactDivision field kernels roots buffers factors stack meter

end BulksketchBridge.RootDivide
