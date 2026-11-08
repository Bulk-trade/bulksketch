import Arithmetic.RebuiltLfsrGenerated
import BulksketchBridge.DenseCoefficientPolynomial
import BulksketchBridge.ReconciliationLfsrSpec

namespace BulksketchBridge.RebuiltLfsr

open Aeneas.Std Algebra.Gf64 DenseCoefficient SliceKernelChallenges
open bulksketch.backend.contract

def restorePrefix (buffer replacement : Slice U64) : Slice U64 :=
  Slice.from (buffer.val.setSlice! 0 replacement.val) (by simp)

def zeroWords (shape : Slice U64) : Slice U64 :=
  Slice.from (List.replicate shape.length 0#u64) (by simp)

def linearStep (words : Slice U64) (root : U64) : Slice U64 :=
  Slice.from (List.ofFn fun index : Fin words.length =>
    coefficientAfter words root index.val) (by simp)

def locatorStep (words : Slice U64) (root : U64) (stop : Nat) : Slice U64 :=
  restorePrefix words (linearStep (prefixSlice words stop) root)

def locatorFrom (roots : Slice U64) (current : Slice U64) (index : Nat) : Nat → Slice U64
  | 0 => current
  | count + 1 => locatorFrom roots (locatorStep current roots[index]! (index + 2)) (index + 1) count

def locatorWords (roots shape : Slice U64) : Slice U64 :=
  locatorFrom roots ((zeroWords shape).setAtNat 0 1#u64) 0 roots.length

def squareFrom (words : Slice U64) (start : Nat) : Slice U64 :=
  Slice.from (List.ofFn fun index : Fin words.length =>
    if start ≤ index.val then Square.expectedWord words[index.val]! else words[index.val]!)
    (by simp)

def squaringLaw {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) : Prop :=
  ∀ input, kernels.ArithmeticInst.square input =
    bulksketch.field.gf64.square bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField input

def linearLaw {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) : Prop :=
  ∀ words root, kernels.multiply_linear words root = Result.ok (linearStep words root)

/-- Result and complete scratch frames of the original wrapper with
explicit contracts for the independent backend callbacks. -/
def ActualRebuiltLfsrReturnsFrames : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    linearLaw kernels → squaringLaw kernels →
    ∀ (roots odd coefficients expected seed : Slice U64),
      roots.length < coefficients.length →
      min roots.length odd.length ≤ expected.length →
      seed.length = min roots.length odd.length →
      kernels.insert_nonzero (zeroWords (prefixSlice expected seed.length)) roots = Result.ok seed →
      let locator := locatorWords roots (prefixSlice coefficients (roots.length + 1))
      let squared := squareFrom locator 1
      (seed = prefixSlice odd seed.length → ∃ result,
        kernels.odd_recurrence_matches odd squared = Result.ok result) →
      ∃ result,
        bulksketch.decode.verify.rebuilt_lfsr
          bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField kernels roots odd coefficients expected =
          Result.ok (result,
            restorePrefix coefficients (if seed = prefixSlice odd seed.length then squared else locator),
            restorePrefix expected seed) ∧
        if seed = prefixSlice odd seed.length then
          kernels.odd_recurrence_matches odd squared = Result.ok result
        else result = false

end BulksketchBridge.RebuiltLfsr
