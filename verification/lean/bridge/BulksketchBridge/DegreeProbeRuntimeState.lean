import BulksketchBridge.DegreeProbeRuntimeStateSpec

namespace BulksketchBridge.DegreeProbeRuntime

open Aeneas Aeneas.Std bulksketch.decode.degree_probe bulksketch.decode.row

theorem new_refines : ActualDegreeProbeNew := by
  intro budget capacity
  have budgetFits : 3#usize ≤ budget.nonzero ↔ 3 ≤ budget.nonzero.val := by simp [UScalar.le_equiv]
  have capacityFits : 3#usize ≤ capacity ↔ 3 ≤ capacity.val := by simp [UScalar.le_equiv]
  by_cases enoughBudget : 3 ≤ budget.nonzero.val
  · by_cases enoughCapacity : 3 ≤ capacity.val
    · simp [DegreeProbe.new, CubeRootRuntime.thenSome, expectedNew, initialState, budgetFits, capacityFits,
        enoughBudget, enoughCapacity, bind_ok]
    · simp [DegreeProbe.new, CubeRootRuntime.thenSome, expectedNew, budgetFits, capacityFits,
        enoughBudget, enoughCapacity, bind_ok]
  · simp [DegreeProbe.new, CubeRootRuntime.thenSome, expectedNew, budgetFits, enoughBudget, bind_ok]

theorem next_stage_refines : ActualDegreeProbeNextStage := by
  intro self
  rfl

theorem count_refines : ActualDegreeProbeCount := by
  intro self
  refine ⟨core.convert.num.FromUsizeU8.from self.count, rfl, ?_⟩
  exact U8.cast_Usize_val_eq _

theorem reject_refines : ActualDegreeProbeReject := by
  intro self capacity budget
  have degreeThree : self.degree = 3#u8 ↔ self.degree.val = 3 := by simp [UScalar.eq_equiv]
  have capacityFits : 4#usize ≤ capacity ↔ 4 ≤ capacity.val := by simp [UScalar.le_equiv]
  have budgetFits : 4#usize ≤ budget.nonzero ↔ 4 ≤ budget.nonzero.val := by simp [UScalar.le_equiv]
  by_cases three : self.degree.val = 3
  · by_cases enoughCapacity : 4 ≤ capacity.val
    · by_cases enoughBudget : 4 ≤ budget.nonzero.val <;>
        simp [DegreeProbe.reject, expectedReject, degreeThree, capacityFits, budgetFits, three, enoughCapacity, enoughBudget]
    · simp [DegreeProbe.reject, expectedReject, degreeThree, capacityFits, three, enoughCapacity]
  · simp [DegreeProbe.reject, expectedReject, degreeThree, three]

/-- A successful constructor fixes the initial stage and supplies the two bounds. -/
theorem new_some_iff (budget : RowBudget) (capacity : Usize) (self : DegreeProbe) :
    DegreeProbe.new budget capacity = .ok (some self) ↔
      self = initialState ∧ 3 ≤ budget.nonzero.val ∧ 3 ≤ capacity.val := by
  rw [new_refines budget capacity]
  by_cases admitted : 3 ≤ budget.nonzero.val ∧ 3 ≤ capacity.val
  · simp [expectedNew, admitted, eq_comm]
  · simp [expectedNew, admitted]

/-- Every rejection clears the candidate count. The guard-four transition
is exactly the original degree-three case with both larger bounds. -/
theorem reject_post (self : DegreeProbe) (capacity : Usize) (budget : RowBudget) :
    ∃ rejected : DegreeProbe,
      DegreeProbe.reject self capacity budget = .ok rejected ∧
      rejected.count = 0#u8 ∧
      (rejected.next = some .GuardFour ↔ self.degree.val = 3 ∧ 4 ≤ capacity.val ∧ 4 ≤ budget.nonzero.val) ∧
      (rejected.next = some .GuardFour → rejected.degree = 4#u8) ∧
      (rejected.next = some .Reconstruction → rejected.degree = self.degree) := by
  refine ⟨expectedReject self capacity budget, reject_refines self capacity budget, ?_⟩
  by_cases admit : self.degree.val = 3 ∧ 4 ≤ capacity.val ∧ 4 ≤ budget.nonzero.val <;>
    simp [expectedReject, admit]

end BulksketchBridge.DegreeProbeRuntime
