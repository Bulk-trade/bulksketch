import Arithmetic.QuarticGenerated
import BulksketchBridge.RebuiltLfsrSpec
import BulksketchBridge.CubicSpec

namespace BulksketchBridge.QuarticSolve

open Aeneas.Std bulksketch.backend.contract bulksketch.decode.deg34

abbrev fieldDictionary := bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField

/-- A miss preserves all output words. A hit copies the original candidates into the admitted prefix. -/
def expectedFrame {size : Usize} (output : Slice U64) (candidates : Option (Array U64 size)) :
    Option Usize × Slice U64 :=
  match candidates with
  | none => (none, output)
  | some words => (some size, RebuiltLfsr.restorePrefix output words.to_slice)

def ActualSolveCubicFrame : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (factor output : Slice U64) (candidates : Option (Array U64 3#usize)),
    factor.length = 4 → 3 ≤ output.length →
    cubic fieldDictionary kernels factor[2]! factor[1]! factor[0]! = Result.ok candidates →
    solve fieldDictionary kernels factor output = Result.ok (expectedFrame output candidates)

def ActualSolveQuarticFrame : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (factor output : Slice U64) (candidates : Option (Array U64 4#usize)),
    factor.length = 5 → 4 ≤ output.length →
    quartic fieldDictionary kernels factor = Result.ok candidates →
    solve fieldDictionary kernels factor output = Result.ok (expectedFrame output candidates)

def ActualSolveCandidateFrames : Prop := ActualSolveCubicFrame ∧ ActualSolveQuarticFrame

/-- The original entry returns normally on admitted calls and copies exactly
the candidates of the selected original cubic or quartic. -/
def ActualSolveReturnsExactFrame : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) (factor output : Slice U64),
    Cubic.CorrectArithmetic kernels → (factor.length = 4 ∨ factor.length = 5) →
    factor.length - 1 ≤ output.length →
    ∃ result, solve fieldDictionary kernels factor output = Result.ok result ∧
      (factor.length = 4 → ∃ candidates,
        cubic fieldDictionary kernels factor[2]! factor[1]! factor[0]! = Result.ok candidates ∧
        result = expectedFrame output candidates) ∧
      (factor.length = 5 → ∃ candidates, quartic fieldDictionary kernels factor = Result.ok candidates ∧
        result = expectedFrame output candidates)

end BulksketchBridge.QuarticSolve
