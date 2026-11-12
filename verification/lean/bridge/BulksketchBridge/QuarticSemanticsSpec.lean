import BulksketchBridge.QuarticControlSpec
import BulksketchBridge.QuarticReciprocal

namespace BulksketchBridge.QuarticSemantics

open Aeneas.Std Algebra.Gf64 bulksketch.backend.contract
open QuarticControl

def RecoveryGate {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (a b c d : U64) : Prop :=
  match prepare a b c d with
  | none => False
  | some (.direct b c _) | some (.shifted b c _ _) =>
    c ≠ 0#u64 ∧ AffineQuartic.CertifiedKernel kernels b c

noncomputable def evaluate (a b c d : U64) (z : Field) : Field :=
  QuarticReciprocal.evaluate (toField a.bv) (toField b.bv) (toField c.bv) (toField d.bv) z

def FourRoots (a b c d : U64) (roots : Words) : Prop :=
  roots.val.Nodup ∧ ∀ word ∈ roots.val, evaluate a b c d (toField word.bv) = 0

/-- All four successful words solve the original monic quartic. Success
requires the exact native recovery gate, including its denominator check,
and is complete once that gate accepts. -/
def ActualQuarticRefines : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) (factor : Slice U64),
    Cubic.CorrectArithmetic kernels → 4 ≤ factor.length →
    let (a, b, c, d) := (factor[3]!, factor[2]!, factor[1]!, factor[0]!)
    ∃ output, bulksketch.decode.deg34.quartic fieldDictionary kernels factor = .ok output ∧
      (∀ roots, output = some roots → FourRoots a b c d roots) ∧
      ((∃ roots, output = some roots) ↔ RecoveryGate kernels a b c d ∧
        ∃ z : Field, evaluate a b c d z = 0)

end BulksketchBridge.QuarticSemantics
