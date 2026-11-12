import BulksketchBridge.NativeDeflateResidual

namespace BulksketchBridge.Deflation

open Aeneas.Std DenseCoefficient RebuiltLfsr SliceKernels Algebra.Gf64 Polynomial
open bulksketch.decode.scratch bulksketch.decode.stages

theorem joined_locator_prefix {K : Type} (self : Execution bulksketch.field.Gf64 K)
    (workspace : RowWorkspace) (width : Nat) (locator quotient : Slice U64) (count : Nat)
    (fits : width ≤ workspace.bm.length) (locLen : locator.length = width) (active : count ≤ width) :
    prefixSlice (joinedWorkspace (deflateFrame self workspace width) locator quotient).bm count =
      prefixSlice locator count := by
  let tail := BmEntry.tail workspace.bm width
  have tailLen : (restorePrefix tail quotient).length = workspace.bm.length - width := by
    rw [restore_length, BmEntry.tail_length]
  have shape : locator.length = min width workspace.bm.length ∧
      (restorePrefix tail quotient).length = workspace.bm.length - width := by
    exact ⟨locLen.trans (Nat.min_eq_left fits).symm, tailLen⟩
  apply Slice.ext
  simp only [prefixSlice, Slice.from_val]
  change (BmEntry.splitBack workspace.bm width (locator, restorePrefix tail quotient)).val.take count =
    locator.val.take count
  rw [BmEntry.splitBack, dite_eq_left shape, Slice.from_val]
  exact List.take_append_of_le_length (by change count ≤ locator.length; omega)

theorem started_locator_prefix {K : Type} (self : Execution bulksketch.field.Gf64 K)
    (workspace : RowWorkspace) (width : Nat) (final : FinalState)
    (fits : width ≤ workspace.bm.length) (locLen : final.locator.length = width)
    (degreeRoom : final.degree.val < width) (polyRoom : final.degree.val < workspace.polynomials.length)
    (positive : final.degree ≠ 0#usize) :
    let joined := joinedWorkspace (deflateFrame self workspace width) final.locator final.quotient
    prefixSlice (RootSetup.startedWorkspace final.degree joined).polynomials (final.degree.val + 1) =
      prefixSlice final.locator (final.degree.val + 1) := by
  dsimp only [RootSetup.startedWorkspace]
  rw [ite_eq_right positive, joined_locator_prefix self workspace width final.locator final.quotient
    (final.degree.val + 1) fits locLen (by omega)]
  have copiedLength : (prefixSlice final.locator (final.degree.val + 1)).length = final.degree.val + 1 := by
    rw [prefix_length, Nat.min_eq_left (by omega)]
  have copied := DenseGcd.prefix_restored workspace.polynomials
    (prefixSlice final.locator (final.degree.val + 1)) (by omega)
  rwa [copiedLength] at copied

theorem root_product_monic_of_degree (roots : Slice U64) (index count : Nat) :
    (rootProduct roots index count).Monic ∧ (rootProduct roots index count).natDegree = count := by
  induction count generalizing index with
  | zero => exact ⟨monic_one, natDegree_one⟩
  | succ count ih =>
    rw [rootProduct]
    obtain ⟨monic, degree⟩ := ih (index + 1)
    refine ⟨(monic_X_add_C _).mul monic, ?_⟩
    rw [(monic_X_add_C _).natDegree_mul monic, natDegree_X_add_C, degree, Nat.add_comm]

theorem residual_monic_of_degree (initial residual : Polynomial Field) (roots : Slice U64)
    (index count degree : Nat) (product : initial = rootProduct roots index count * residual)
    (monic : initial.Monic) (degreeEq : initial.natDegree = count + degree) :
    residual.Monic ∧ residual.natDegree = degree := by
  rw [product] at monic degreeEq
  obtain ⟨factorMonic, factorDegree⟩ := root_product_monic_of_degree roots index count
  have residualMonic := factorMonic.of_mul_monic_left monic
  rw [factorMonic.natDegree_mul residualMonic, factorDegree] at degreeEq
  exact ⟨residualMonic, by omega⟩

theorem residual_traversal_invariants (initial residual : Polynomial Field) (roots : Slice U64)
    (index count degree : Nat) (product : initial = rootProduct roots index count * residual)
    (monic : initial.Monic) (degreeEq : initial.natDegree = count + degree)
    (splits : initial.Splits) (simple : Squarefree initial) :
    residual.Monic ∧ residual.natDegree = degree ∧ residual.Splits ∧ Squarefree residual := by
  have divides : residual ∣ initial := ⟨rootProduct roots index count, product.trans (mul_comm ..)⟩
  obtain ⟨residualMonic, residualDegree⟩ :=
    residual_monic_of_degree initial residual roots index count degree product monic degreeEq
  exact ⟨residualMonic, residualDegree, splits.of_dvd monic.ne_zero divides,
    simple.squarefree_of_dvd divides⟩

#print axioms started_locator_prefix
#print axioms residual_traversal_invariants

end BulksketchBridge.Deflation
