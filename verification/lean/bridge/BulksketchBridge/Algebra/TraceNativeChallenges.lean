import BulksketchBridge.Algebra.TraceSpec
import Arithmetic.Funs

/-! Whole-byte normal-return contracts for the unchanged source trace functions,
with Mathlib's algebra trace as the mathematical target. -/

namespace BulksketchBridge.Algebra.Gf64.TraceNativeChallenges

open Aeneas Aeneas.Std

def actualTraceIsAlgebraTrace : Prop :=
  ∀ input : U64, ∃ output : U8,
    bulksketch.field.maps.trace
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField input = Result.ok output ∧
    output.val ≤ 1 ∧
    Algebra.trace (ZMod 2) Field (toField input.bv) = (output.val : ZMod 2)

def actualCanonicalTraceIsAlgebraTrace : Prop :=
  ∀ input : U64, ∃ output : U8,
    bulksketch.field.maps.canonical_trace
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField input = Result.ok output ∧
    output.val ≤ 1 ∧
    Algebra.trace (ZMod 2) Field (toField input.bv) = (output.val : ZMod 2)

end BulksketchBridge.Algebra.Gf64.TraceNativeChallenges
