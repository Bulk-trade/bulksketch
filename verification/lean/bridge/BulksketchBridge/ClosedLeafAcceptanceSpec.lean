import BulksketchBridge.ClosedLeafSpec
import BulksketchBridge.ClosedLeafAdvanceSpec
import BulksketchBridge.CertificatePolynomial

namespace BulksketchBridge.ClosedLeaf

open Aeneas.Std Algebra.Gf64 Polynomial
open bulksketch.types bulksketch.decode.roots bulksketch.decode.scratch bulksketch.backend.contract
open scoped BigOperators

/-- The actual product check accepts exactly a distinct nonzero factorization
of the current factor, with the expected number of roots. -/
def ActualClosedLeafCertificateMeaning : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (workspace : RowWorkspace),
    Cubic.CorrectArithmetic kernels → Admitted roots .FactorVerification workspace →
    ((certificateResult roots workspace).1 = true ↔
      roots.solved_count.val = roots.degree.val ∧
      Certificate.ValidRoots (candidateWords roots workspace) ∧
      SliceKernels.slicePolynomial (factorWords roots workspace) =
        ∏ i ∈ Finset.range (candidateWords roots workspace).length,
          (X + C (toField (candidateWords roots workspace)[i]!.bv)))

/-- On acceptance the original caller appends exactly the certified roots
and either finishes verification or restores the admitted pending frame. -/
def ActualClosedLeafAcceptedAdvance : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (workspace : RowWorkspace) (meter finalMeter : WorkMeter) (product : Slice U64),
    Cubic.CorrectArithmetic kernels → Admitted roots .FactorVerification workspace →
    StageCharge.chargeResult meter (.Ok (leafPrice roots .FactorVerification)) = (.Ok (), finalMeter) →
    certificateResult roots workspace = (true, product) →
    ∃ count : Usize, count.val = roots.count.val + roots.degree.val ∧
      let updated := { roots with count }
      let scratch := acceptedWorkspace roots workspace product
      (roots.pending = 0#usize →
        Roots.closed_leaf fieldDictionary kernels roots .FactorVerification workspace meter =
          Result.ok (normalReturn .Verification updated scratch finalMeter)) ∧
      (∀ frame, ClosedLeafAdvance.PopBounds updated scratch frame →
        let popped := ClosedLeafAdvance.poppedRoots updated scratch frame
        Roots.closed_leaf fieldDictionary kernels roots .FactorVerification workspace meter =
          Result.ok (normalReturn (ClosedLeafAdvance.stageFor popped) popped
            (ClosedLeafAdvance.poppedWorkspace scratch frame) finalMeter))

end BulksketchBridge.ClosedLeaf
