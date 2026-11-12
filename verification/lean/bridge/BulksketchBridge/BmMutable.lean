import BulksketchBridge.BmMutableSpec
import BulksketchBridge.Algebra.WordNative

namespace BulksketchBridge.BmMutable

open Aeneas Aeneas.Std
open bulksketch.backend.contract bulksketch.decode.bm

set_option maxRecDepth 2048

private theorem run_pending {S : Type} (stateAt : Nat → S) (write : Nat → S → S) (stop : Nat)
    (body : Pending S → Result (ControlFlow (Pending S) (Pending S)))
    (step : ∀ index < stop, ∀ back,
      body (stateAt index, back) = .ok (.cont (stateAt (index + 1), fun later => back (write index later))))
    (done : ∀ back, body (stateAt stop, back) = .ok (.done (stateAt stop, back)))
    (start : Nat) (bound : start ≤ stop) (back : S → S) :
    loop body (stateAt start, back) =
      .ok (stateAt stop, fun later => back (writesFrom write start (stop - start) later)) := by
  suffices run : ∀ count start, start ≤ stop → stop - start = count → ∀ back,
      loop body (stateAt start, back) =
        .ok (stateAt stop, fun later => back (writesFrom write start count later)) from
    run _ start bound rfl back
  intro count
  induction count with
  | zero =>
    intro start bounded countEq back
    have terminal : start = stop := by omega
    subst start
    unfold loop
    simp only [done, bind_ok, writesFrom]
  | succ count ih =>
    intro start bounded countEq back
    have active : start < stop := by omega
    have next := ih (start + 1) (by omega) (by omega) (fun later => back (write start later))
    unfold loop
    rw [step start active back]
    simp only [bind_ok]
    rw [next]
    rfl

private theorem mul_normal {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (mul : NativeMul kernels) (left right : U64) :
    kernels.ArithmeticInst.mul left right = .ok (mulWord left right) :=
  (mul left right).trans (Algebra.Gf64.native_mul_word left right)

private theorem next_iter (original : Slice U64) (index : Nat) (bound : index < original.length) :
    core.slice.iter.IteratorIterMut.next (⟨original, index⟩ : Iter) =
      .ok (some original[index]!, ⟨original, index + 1⟩, fun later replacement =>
        match replacement with
        | none => later
        | some word => replaceIter later index word) := by
  have active : index < original.len.val := by simpa using bound
  have exactStep : core.slice.iter.IteratorIterMut.next (⟨original, index⟩ : Iter) =
      Result.ok (some (original[index]'bound), ⟨original, index + 1⟩,
        fun later replacement => match replacement with
          | none => later
          | some word => replaceIter later index word) := by
    unfold core.slice.iter.IteratorIterMut.next
    split
    · dsimp only
      congr 3
      funext later replacement
      cases replacement <;> rfl
    · rename_i stopped
      exact False.elim (stopped active)
  exact exactStep.trans (congrArg (fun word => Result.ok
    (some word, (⟨original, index + 1⟩ : Iter),
      fun (later : Iter) (replacement : Option U64) => match replacement with
        | none => later
        | some replacement => replaceIter later index replacement))
    (Slice.Inhabited_getElem_eq_getElem! original index bound))

private theorem end_iter (original : Slice U64) :
    core.slice.iter.IteratorIterMut.next (⟨original, original.length⟩ : Iter) =
      .ok (none, ⟨original, original.length⟩, fun later _ => later) := by
  unfold core.slice.iter.IteratorIterMut.next
  have stopped : ¬ (⟨original, original.length⟩ : Iter).i < original.len.val := by simp
  rw [dite_eq_right stopped]

private theorem scale_loop2 {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (mul : NativeMul kernels) (original : Slice U64) (start : Nat) (back : Iter → Iter) (scale : U64)
    (bound : start ≤ original.length) :
    locator_loop0_loop2 fieldDictionary kernels ⟨original, start⟩ back scale =
      .ok (iterResult original (mulWord scale) start back) := by
  unfold locator_loop0_loop2 iterResult
  refine run_pending (fun index => (⟨original, index⟩ : Iter))
    (fun index later => replaceIter later index (mulWord scale original[index]!)) original.length _ ?_ ?_ start bound back
  · intro index active restore
    change locator_loop0_loop2.body fieldDictionary kernels scale ⟨original, index⟩ restore = _
    simp only [locator_loop0_loop2.body, next_iter original index active, bind_ok, mul_normal kernels mul]
    rfl
  · intro restore
    change locator_loop0_loop2.body fieldDictionary kernels scale ⟨original, original.length⟩ restore = _
    simp only [locator_loop0_loop2.body, end_iter, bind_ok]
    rfl

theorem scale_loops_refine : ActualBmScaleLoops := by
  intro K kernels mul original start back scale bound
  have exactLoop := scale_loop2 kernels mul original start back scale bound
  exact ⟨exactLoop, exactLoop, exactLoop, exactLoop⟩

theorem normalize_loop_refines : ActualBmNormalizeLoop := by
  intro K kernels mul original start back inverse bound
  unfold locator_loop0_loop0 iterResult
  refine run_pending (fun index => (⟨original, index⟩ : Iter))
    (fun index later => replaceIter later index (mulWord original[index]! inverse)) original.length _ ?_ ?_ start bound back
  · intro index active restore
    change locator_loop0_loop0.body fieldDictionary kernels inverse ⟨original, index⟩ restore = _
    simp only [locator_loop0_loop0.body, next_iter original index active, bind_ok, mul_normal kernels mul]
    rfl
  · intro restore
    change locator_loop0_loop0.body fieldDictionary kernels inverse ⟨original, original.length⟩ restore = _
    simp only [locator_loop0_loop0.body, end_iter, bind_ok]
    rfl

private theorem xor_loop3 {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (mul : NativeMul kernels) (left right : Slice U64) (start : Nat) (back : Zip → Zip) (delta : U64)
    (bound : start ≤ min left.length right.length) :
    locator_loop0_loop3 fieldDictionary kernels (MutableZip.stateAt left right start) back delta =
      .ok (zipResult left right delta start back) := by
  unfold locator_loop0_loop3 zipResult
  refine run_pending (MutableZip.stateAt left right)
    (fun index later => MutableZip.replaceLeft later index (shiftedWord delta left[index]! right[index]!))
    (min left.length right.length) _ ?_ ?_ start bound back
  · intro index active restore
    have leftBound := (Nat.lt_min.mp active).1
    have rightBound := (Nat.lt_min.mp active).2
    change locator_loop0_loop3.body fieldDictionary kernels delta (MutableZip.stateAt left right index) restore = _
    simp only [locator_loop0_loop3.body, MutableZip.next_some_at left right index leftBound rightBound, bind_ok]
    dsimp! only
    rw [Slice.Inhabited_getElem_eq_getElem! left index leftBound,
      Slice.Inhabited_getElem_eq_getElem! right index rightBound]
    simp only [mul_normal kernels mul, bind_ok, lift, shiftedWord]
  · intro restore
    change locator_loop0_loop3.body fieldDictionary kernels delta
      (MutableZip.stateAt left right (min left.length right.length)) restore = _
    simp only [locator_loop0_loop3.body, MutableZip.next_done_at left right (min left.length right.length) (by omega), bind_ok]
    rfl

theorem shifted_xor_loops_refine : ActualBmShiftedXorLoops := by
  intro K kernels mul left right start back delta bound
  have exactLoop := xor_loop3 kernels mul left right start back delta bound
  have exactZeroLoop := xor_loop3 kernels mul left right start back 0#u64 bound
  exact ⟨exactLoop, exactZeroLoop, exactLoop, exactZeroLoop⟩

end BulksketchBridge.BmMutable
