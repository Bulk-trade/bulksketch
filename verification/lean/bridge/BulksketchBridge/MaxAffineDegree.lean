import Arithmetic.MaxAffineDegreeGenerated
import BulksketchBridge.RawMulTable

namespace BulksketchBridge.RootWorkBudget

open Aeneas Aeneas.Std
open bulksketch.decode.affine

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

private theorem maximum_degree_loop (degree current : Usize) (fuel : Nat)
    (minimum : 3 ≤ degree.val) (remaining : degree.val + fuel = 64) :
    MAX_PREFERRED_DEGREE_loop degree current =
      .ok (if degree.val ≤ 18 then 18#usize else current) := by
  induction fuel generalizing degree current with
  | zero =>
    have no : ¬ degree.val < 64 := by omega
    have beyond : ¬ degree.val ≤ 18 := by omega
    rw [MAX_PREFERRED_DEGREE_loop, loop]
    simp only [MAX_PREFERRED_DEGREE_loop.body, UScalar.lt_equiv,
      show (64#usize).val = 64 by rfl, no, ite_false, beyond, bind_ok]
  | succ fuel ih =>
    have live : degree.val < 64 := by omega
    have bound : degree.val + 1 ≤ Usize.max := by
      simp only [Usize.max, Usize.numBits, UScalarTy.numBits]
      rcases System.Platform.numBits_eq with platform | platform <;>
        rw [platform] <;> omega
    obtain ⟨next, add, nextValue⟩ := RawMulTable.normal_of_spec _ _
      (Usize.add_spec (x := degree) (y := 1#usize) bound)
    change next.val = degree.val + 1 at nextValue
    have preference := AffinePreferred.native_preferred_refines.2 degree
    change preferred bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField degree =
      .ok (decide (3 ≤ degree.val ∧ degree.val ≤ 18)) at preference
    have nextMinimum : 3 ≤ next.val := by omega
    have nextRemaining : next.val + fuel = 64 := by omega
    rw [MAX_PREFERRED_DEGREE_loop, loop]
    simp only [MAX_PREFERRED_DEGREE_loop.body, UScalar.lt_equiv,
      show (64#usize).val = 64 by rfl, live, ite_true, preference, minimum, true_and, bind_ok]
    by_cases selected : degree.val ≤ 18
    · simp only [selected, decide_true, ite_true, add, bind_ok]
      change MAX_PREFERRED_DEGREE_loop next degree = .ok 18#usize
      rw [ih next degree nextMinimum nextRemaining]
      by_cases earlier : next.val ≤ 18
      · rw [ite_eq_left earlier]
      · have exactDegree : degree = 18#usize := UScalar.eq_of_val_eq (by change degree.val = 18; omega)
        rw [ite_eq_right earlier, exactDegree]
    · simp only [selected, decide_false, Bool.false_eq_true, ite_false, add, bind_ok]
      change MAX_PREFERRED_DEGREE_loop next current = .ok current
      rw [ih next current nextMinimum nextRemaining, ite_eq_right (by omega)]

def ActualNativeMaxPreferredDegree : Prop :=
  MAX_PREFERRED_DEGREE = .ok 18#usize

theorem native_max_preferred_degree : ActualNativeMaxPreferredDegree := by
  unfold ActualNativeMaxPreferredDegree
  rw [MAX_PREFERRED_DEGREE]
  have result := maximum_degree_loop 3#usize 0#usize 61 (by decide) (by decide)
  exact result

#print axioms native_max_preferred_degree

end BulksketchBridge.RootWorkBudget
