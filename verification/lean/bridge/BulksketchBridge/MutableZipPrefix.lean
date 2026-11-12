import BulksketchBridge.MutableZip

namespace BulksketchBridge.MutableZip

open Aeneas Aeneas.Std

/-- The unvisited part of the common Zip prefix. The unmatched destination
tail and any already visited slots retain their original words. -/
def mapPrefixFrom {T U : Type} [Inhabited T] [Inhabited U]
    (left : Slice T) (right : Slice U) (transform : T → U → T) (start : Nat) : Slice T :=
  Slice.from (List.ofFn fun (i : Fin left.length) =>
    if start ≤ i.val ∧ i.val < right.length then transform left[i.val]! right[i.val]!
    else left[i.val]!) (by simp)

@[simp] theorem mapPrefixFrom_length {T U : Type} [Inhabited T] [Inhabited U]
    (left : Slice T) (right : Slice U) (transform : T → U → T) (start : Nat) :
    (mapPrefixFrom left right transform start).length = left.length := by simp [mapPrefixFrom]

theorem mapPrefixFrom_word {T U : Type} [Inhabited T] [Inhabited U]
    (left : Slice T) (right : Slice U) (transform : T → U → T)
    (start i : Nat) (bound : i < left.length) :
    (mapPrefixFrom left right transform start)[i]! =
      if start ≤ i ∧ i < right.length then transform left[i]! right[i]! else left[i]! := by
  simp only [mapPrefixFrom, Slice.getElem!_Nat_eq, Slice.from_val]
  rw [← List.Inhabited_getElem_eq_getElem! _ i (by simpa using bound), List.getElem_ofFn]

private theorem map_end {T U : Type} [Inhabited T] [Inhabited U]
    (left : Slice T) (right : Slice U) (transform : T → U → T) :
    mapPrefixFrom left right transform (min left.length right.length) = left := by
  apply Slice.ext_getElem (by simp)
  intro index mappedBound bound
  rw [Slice.Inhabited_getElem_eq_getElem! _ index mappedBound,
    Slice.Inhabited_getElem_eq_getElem! left index bound,
    mapPrefixFrom_word left right transform _ index bound, ite_eq_right (by omega)]

private theorem apply_prefix_step {T U : Type} [Inhabited T] [Inhabited U]
    (left : Slice T) (right : Slice U) (transform : T → U → T)
    (i : Nat) (bound : i < min left.length right.length) :
    replaceLeft (stateAt (mapPrefixFrom left right transform (i + 1)) right
      (min left.length right.length)) i (transform left[i]! right[i]!) =
        stateAt (mapPrefixFrom left right transform i) right (min left.length right.length) := by
  have update : (mapPrefixFrom left right transform (i + 1)).setAtNat i
      (transform left[i]! right[i]!) = mapPrefixFrom left right transform i := by
    apply Slice.ext_getElem (by simp)
    intro j updatedBound outputBound
    have jBound : j < left.length := by simpa using outputBound
    rw [Slice.Inhabited_getElem_eq_getElem! _ j updatedBound,
      Slice.Inhabited_getElem_eq_getElem! _ j outputBound,
      mapPrefixFrom_word left right transform _ j jBound]
    rw [Slice.getElem!_Nat_eq]
    by_cases same : i = j
    · subst j
      rw [Slice.getElem!_Nat_setAtNat_eq _ _ _ (by simpa using jBound), ite_eq_left (by omega)]
    · rw [Slice.getElem!_Nat_setAtNat_ne _ _ _ _ same, ← Slice.getElem!_Nat_eq,
        mapPrefixFrom_word left right transform _ j jBound]
      have sameGuard : i + 1 ≤ j ↔ i ≤ j := by omega
      simp only [sameGuard]
  simp only [replaceLeft, stateAt, update]

abbrev MapBody (T U : Type) :=
  State T U × (State T U → State T U) →
    Result (ControlFlow (State T U × (State T U → State T U)) (State T U))

/-- The common prefix length decreases at each forward step, and the pending
backward updates restore the complete destination frame. -/
theorem map_prefix_loop {T U : Type} [Inhabited T] [Inhabited U]
    (left : Slice T) (right : Slice U) (transform : T → U → T) (body : MapBody T U)
    (step : ∀ i, i < min left.length right.length → ∀ back,
      body (stateAt left right i, back) =
        Result.ok (ControlFlow.cont (stateAt left right (i + 1),
          fun final => back (replaceLeft final i (transform left[i]! right[i]!)))))
    (done : ∀ back, body (stateAt left right (min left.length right.length), back) =
      Result.ok (ControlFlow.done (back (stateAt left right (min left.length right.length)))))
    (start : Nat) (bound : start ≤ min left.length right.length) (back : State T U → State T U) :
    loop body (stateAt left right start, back) =
      Result.ok (back (stateAt (mapPrefixFrom left right transform start) right
        (min left.length right.length))) := by
  let stop := min left.length right.length
  suffices ∀ remaining start, start ≤ stop → stop - start = remaining →
    ∀ back : State T U → State T U,
      loop body (stateAt left right start, back) =
        Result.ok (back (stateAt (mapPrefixFrom left right transform start) right stop))
    from this (stop - start) start bound rfl back
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
    intro start bounded eq back
    by_cases active : start < stop
    · have rest := ih (stop - (start + 1)) (by omega) (start + 1) (by omega) rfl
        (fun final => back (replaceLeft final start (transform left[start]! right[start]!)))
      unfold loop
      rw [step start active back]
      simp only [bind_ok]
      rw [rest, apply_prefix_step left right transform start active]
    · have terminal : start = stop := by omega
      subst start
      unfold loop
      simp only [stop, done back, bind_ok, map_end]

theorem run_prefix_map (left right : Slice U64) (transform : U64 → U64 → U64)
    (body : MapBody U64 U64)
    (step : ∀ i, i < min left.length right.length → ∀ back,
      body (stateAt left right i, back) =
        Result.ok (ControlFlow.cont (stateAt left right (i + 1),
          fun final => back (replaceLeft final i (transform left[i]! right[i]!)))))
    (done : ∀ back, body (stateAt left right (min left.length right.length), back) =
      Result.ok (ControlFlow.done (back (stateAt left right (min left.length right.length))))) :
    (do
      let (iterMut, restoreSlice) ← core.slice.Slice.iter_mut left
      let (iter, restoreIter) ← bulksketch.core.iter.traits.iterator.Iterator.zip.trait_default
        (bulksketch.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT U64)
        (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter U64) iterMut right
      let final ← loop body (iter, fun state => state)
      Result.ok (restoreSlice (restoreIter final))) =
      Result.ok (mapPrefixFrom left right transform 0) := by
  simp only [core.slice.Slice.iter_mut, bind_ok]
  dsimp! only
  rw [construct]
  simp only [bind_ok]
  dsimp! only
  rw [map_prefix_loop left right transform body step done 0 (Nat.zero_le _) (fun state => state)]
  simp only [bind_ok, stateAt]

end BulksketchBridge.MutableZip
