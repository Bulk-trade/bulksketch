import BulksketchBridge.NewtonGuardPreparation
import BulksketchBridge.NewtonGuardResidual

namespace BulksketchBridge.NewtonGuard

open Aeneas Aeneas.Std Aeneas.Std.WP
open NewtonGuardResidual (residualOK residual_loops_refine)

theorem guard_refines : ActualNewtonGuardRefines := by
  intro K kernels odd degree scratch arithmetic admitted
  rw [guard_preparation_refines kernels odd degree scratch arithmetic admitted]
  have degreeValues : degree.val = 3 ∨ degree.val = 4 := by
    rcases admitted.degreeCases with three | four
    · left; rw [three]; rfl
    · right; rw [four]; rfl
  let words := clearedWords odd degree.val
  by_cases zero : words.2 = 0#u64
  · simp only [prepared, expected, ← show words = clearedWords odd degree.val from rfl, zero, ite_true]
  · let updated := clearedFrame scratch words
    have room := admitted.scratchRoom zero
    have outBound : degree.val ≤ updated.length := by
      change degree.val ≤ (clearedFrame scratch words).length
      rw [clearedFrame_length]
      omega
    obtain ⟨limit, added, limitValue⟩ := RawMulTable.normal_of_spec _ _
      (Usize.add_spec (x := degree) (y := 2#usize)
        (by have : (6 : Nat) ≤ Usize.max := by scalar_tac
            change degree.val + 2 ≤ Usize.max
            omega))
    change limit.val = degree.val + 2 at limitValue
    let iter : core.ops.range.Range Usize :=
      ⟨degree, core.cmp.impls.OrdUsize.min (Slice.len odd) limit⟩
    have iterValue : iter.«end».val = min odd.length (degree.val + 2) := by
      simp only [iter, core.cmp.impls.OrdUsize.min_val, Slice.len_val, limitValue]
    obtain ⟨cubic, quartic⟩ := residual_loops_refine kernels arithmetic iter odd degree updated words.2
      degreeValues (by rfl) (by rw [iterValue]) outBound
    have startValue : iter.start.val = degree.val := rfl
    simp only [iterValue, startValue] at cubic quartic
    rw [← residualOK] at cubic quartic
    simp only [prepared, expected, ← show words = clearedWords odd degree.val from rfl, zero, ite_false,
      added, bind_ok]
    rw [cubic, quartic]
    simp only [ite_self, bind_ok]
    rfl

end BulksketchBridge.NewtonGuard
