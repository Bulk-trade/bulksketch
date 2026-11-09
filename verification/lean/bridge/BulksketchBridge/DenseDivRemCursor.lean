import BulksketchBridge.DenseDivisionNormalized
import BulksketchBridge.InverseUsing
import BulksketchBridge.DenseMulReduction
import BulksketchBridge.BmTerminalSpec

namespace BulksketchBridge.DenseDivision

open Aeneas Aeneas.Std Algebra.Gf64
open bulksketch.backend.contract
open scoped BulksketchBridge.DenseMulReductionSpec

set_option maxRecDepth 4096

abbrev ReverseRange := core.iter.adapters.rev.Rev (core.ops.range.Range Usize)

def reverseRange (start stop : Usize) : ReverseRange := ⟨⟨start, stop⟩⟩

abbrev nextReverse := core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
  (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize)

private theorem range_test (start stop : Usize) :
    core.iter.range.StepUsize.partialOrdInst.lt start stop =
      .ok (decide (start.val < stop.val)) := rfl

theorem reverse_next (start stop top : Usize) (active : start.val < stop.val)
    (decremented : stop.val = top.val + 1) :
    nextReverse (reverseRange start stop) = .ok (some top, reverseRange start top) := by
  have test : core.iter.range.StepUsize.partialOrdInst.lt start stop = .ok true := by
    rw [range_test]
    simp only [active, decide_true]
  have fits : (1#usize).val ≤ stop.val := by change 1 ≤ stop.val; omega
  have backward : core.iter.range.StepUsize.backward_checked stop 1#usize = .ok (some top) := by
    change core.iter.range.UScalarStep.backward_checked stop 1#usize = _
    unfold core.iter.range.UScalarStep.backward_checked
    rw [dite_eq_left fits]
    congr 2
    apply UScalar.eq_of_val_eq
    change stop.val - 1 = top.val
    omega
  have normal :
      core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back core.iter.range.StepUsize
        ⟨start, stop⟩ = .ok (some top, ⟨start, top⟩) := by
    simp only [core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back, test, bind_ok, ite_true]
    change Aeneas.Std.bind (core.iter.range.StepUsize.backward_checked stop 1#usize) _ = _
    rw [backward, bind_ok]
  simp only [nextReverse, reverseRange, core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    normal, bind_ok]
  rfl

theorem reverse_done (start stop : Usize) (exhausted : stop.val ≤ start.val) :
    nextReverse (reverseRange start stop) = .ok (none, reverseRange start stop) := by
  have test : core.iter.range.StepUsize.partialOrdInst.lt start stop = .ok false := by
    rw [range_test]
    simp only [Nat.not_lt.mpr exhausted, decide_false]
  simp only [nextReverse, reverseRange, core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.DoubleEndedIterator,
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back, test, bind_ok,
    Bool.false_eq_true, ite_false]
  rfl

theorem native_inverse {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (law : BmTerminal.NativeInverse kernels) (leading : U64) (nonzero : leading ≠ 0#u64) :
    (if leading = 1#u64 then Result.ok 1#u64 else do
      let option ← kernels.ArithmeticInst.inverse leading
      core.option.Option.expect option (toStr "noncanonical polynomial divisor")) = .ok (divisorInverse leading) := by
  by_cases one : leading = 1#u64
  · simp only [one, ite_true, divisorInverse]
  · rw [ite_eq_right one, law, InverseUsing.inverse_refines]
    simp only [Inverse.expectedFieldInverse, nonzero, ite_false, bind_ok, core.option.Option.expect,
      divisorInverse, one, DirectTwo.inverseWord]
    rfl

end BulksketchBridge.DenseDivision
