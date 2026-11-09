import BulksketchBridge.NativeDeflateOuterStep
import BulksketchBridge.DenseGcd

namespace BulksketchBridge.Deflation

open Aeneas Aeneas.Std Result DenseCoefficient RebuiltLfsr SliceKernels Algebra.Gf64
open bulksketch.backend.contract bulksketch.decode.stages.Execution

set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

def rootCursor (roots : Slice U64) (index : Nat) : RootCursor := ⟨roots, index⟩

private theorem cursor_active (roots : Slice U64) (index : Nat) (active : index < roots.length) :
    core.slice.iter.IteratorSliceIter.next (rootCursor roots index) =
      .ok (some roots[index]!, rootCursor roots (index + 1)) := by
  have step : index < (Slice.len roots).val := by rwa [Slice.len_val]
  unfold rootCursor core.slice.iter.IteratorSliceIter.next
  dsimp only
  rw [dite_eq_left step]
  exact congrArg (fun item => Result.ok (some item, rootCursor roots (index + 1)))
    (Slice.Inhabited_getElem_eq_getElem! roots index active)

private theorem cursor_exhausted (roots : Slice U64) (index : Nat) (endReached : roots.length ≤ index) :
    core.slice.iter.IteratorSliceIter.next (rootCursor roots index) =
      .ok (none, rootCursor roots index) := by
  have stopped : ¬ index < (Slice.len roots).val := by rw [Slice.len_val]; omega
  unfold rootCursor core.slice.iter.IteratorSliceIter.next
  dsimp only
  rw [dite_eq_right stopped]

/-- The exact root pass stops at the first failed synthetic division. Each
successful step divides the active locator by its actual next linear factor
and restores only the prefix of the locator. Exhaustion calls Roots.start
with the final buffers, and rejection keeps the current locator unchanged. -/
inductive DeflateTrace (frame : DeflateFrame) (roots : Slice U64) :
    Nat → Slice U64 → Slice U64 → Usize → Result DeflateAnswer → Prop
  | exhausted (index : Nat) (locator quotient : Slice U64) (degree : Usize)
      (atEnd : index = roots.length) :
      DeflateTrace frame roots index locator quotient degree (startOutput frame locator quotient degree)
  | rejected (index : Nat) (locator quotient : Slice U64) (degree : Usize)
      (active : index < roots.length)
      (notRoot : ¬ (slicePolynomial (prefixSlice locator (degree.val + 1))).IsRoot
        (toField roots[index]!.bv)) :
      DeflateTrace frame roots index locator quotient degree
        (.ok (rejectOutput frame locator (syntheticOutput locator quotient roots[index]! degree)))
  | accepted (index : Nat) (locator quotient : Slice U64) (degree lower : Usize)
      (output : Result DeflateAnswer)
      (active : index < roots.length) (decreased : lower.val + 1 = degree.val)
      (identity : slicePolynomial (prefixSlice locator (degree.val + 1)) =
        (Polynomial.X + Polynomial.C (toField roots[index]!.bv)) *
          slicePolynomial (prefixSlice (syntheticOutput locator quotient roots[index]! degree) degree.val))
      (rest : DeflateTrace frame roots (index + 1)
        (restorePrefix locator (prefixSlice (syntheticOutput locator quotient roots[index]! degree) degree.val))
        (syntheticOutput locator quotient roots[index]! degree) lower output) :
      DeflateTrace frame roots index locator quotient degree output

private theorem outer_once {K : Type} (field : bulksketch.field.BinaryField bulksketch.field.Gf64)
    (kernels : BulkKernels K bulksketch.field.Gf64) (frame : DeflateFrame)
    (iterator : RootCursor) (locator quotient : Slice U64) (degree : Usize) :
    outerLoop field kernels frame iterator locator quotient degree = (do
      let step ← outerBody field kernels frame iterator locator quotient degree
      match step with
      | .done output => .ok output
      | .cont (next, updated, scratch, lower) => outerLoop field kernels frame next updated scratch lower) := by
  rw [outer_loop_eq, loop]
  dsimp! only
  congr 1
  funext step
  cases step with
  | done output => rfl
  | cont state => rcases state with ⟨next, locator, quotient, degree⟩; rfl

def ActualNativeDeflateOuter : Prop :=
  ∀ {K : Type} (field : bulksketch.field.BinaryField bulksketch.field.Gf64)
    (kernels : BulkKernels K bulksketch.field.Gf64)
    (_mul : ∀ a b, kernels.ArithmeticInst.mul a b = .ok (mulWord a b))
    (frame : DeflateFrame) (roots : Slice U64) (index : Nat)
    (locator quotient : Slice U64) (degree : Usize),
    index ≤ roots.length → roots.length - index ≤ degree.val →
    degree.val < locator.length → degree.val ≤ quotient.length →
    DeflateTrace frame roots index locator quotient degree
      (outerLoop field kernels frame (rootCursor roots index) locator quotient degree)

theorem native_deflate_outer : ActualNativeDeflateOuter := by
  intro K field kernels mul frame roots index locator quotient degree bounded available locatorRoom quotientRoom
  suffices ∀ remaining index locator quotient (degree : Usize),
      index ≤ roots.length → roots.length - index ≤ degree.val →
      degree.val < locator.length → degree.val ≤ quotient.length → roots.length - index = remaining →
      DeflateTrace frame roots index locator quotient degree
        (outerLoop field kernels frame (rootCursor roots index) locator quotient degree) by
    exact this _ index locator quotient degree bounded available locatorRoom quotientRoom rfl
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
    intro index locator quotient degree bounded available locatorRoom quotientRoom measure
    rw [outer_once]
    by_cases atEnd : index = roots.length
    · have yielded := cursor_exhausted roots index (by omega)
      rw [outer_exhausted field kernels frame _ _ locator quotient degree yielded]
      simpa only [Aeneas.Std.bind_assoc, bind_ok,
        Aeneas.Std.bind_pure] using DeflateTrace.exhausted (frame := frame) (roots := roots) index locator quotient degree atEnd
    · have active : index < roots.length := by omega
      have positive : 0 < degree.val := by omega
      obtain ⟨lower, lowered, step⟩ := outer_root field kernels mul frame _ _ locator quotient
        roots[index]! degree (cursor_active roots index active) positive locatorRoom quotientRoom
      rw [step]
      let output := syntheticOutput locator quotient roots[index]! degree
      have math := (native_synthetic_step field kernels mul locator quotient roots[index]! degree
        positive locatorRoom quotientRoom).2.2
      change (slicePolynomial (prefixSlice locator (degree.val + 1)) =
        (Polynomial.X + Polynomial.C (toField roots[index]!.bv)) *
          slicePolynomial (prefixSlice output degree.val) +
          Polynomial.C (toField (remainderWord locator output roots[index]!).bv)) ∧
        (remainderWord locator output roots[index]! = 0#u64 ↔
          (slicePolynomial (prefixSlice locator (degree.val + 1))).IsRoot (toField roots[index]!.bv))
        at math
      by_cases zero : remainderWord locator output roots[index]! = 0#u64
      · rw [ite_eq_right (show ¬ remainderWord locator output roots[index]! ≠ 0#u64 from
          fun nonzero => nonzero zero), bind_ok]
        have outputLength : output.length = quotient.length := synthetic_output_length ..
        have rest := ih (roots.length - (index + 1)) (by omega) (index + 1)
          (restorePrefix locator (prefixSlice output degree.val)) output lower (by omega) (by omega)
          (by rw [restore_length]; omega) (by omega) rfl
        refine DeflateTrace.accepted (frame := frame) (roots := roots) index locator quotient degree lower _ active (by omega) ?_ rest
        have identity := math.1
        rw [zero, show toField (0#u64).bv = 0 from toField_zero, Polynomial.C_0, add_zero] at identity
        exact identity
      · rw [ite_eq_left zero, bind_ok]
        exact DeflateTrace.rejected (frame := frame) (roots := roots) index locator quotient degree active
          (fun root => zero (math.2.mpr root))

#print axioms native_deflate_outer

end BulksketchBridge.Deflation
