import BulksketchBridge.MutableZip

namespace BulksketchBridge.MutableZip

open Aeneas Aeneas.Std

/-- The suffix of the equal-length slice transform. Earlier words are retained
until their own backward updates are applied. -/
def mapFrom {α β : Type} [Inhabited α] [Inhabited β]
    (left : Slice α) (right : Slice β) (transform : α → β → α) (start : Nat) : Slice α :=
  Slice.from (List.ofFn fun (i : Fin left.length) =>
    if start ≤ i.val then transform left[i.val]! right[i.val]! else left[i.val]!)
    (by simp)

@[simp] theorem mapFrom_length {α β : Type} [Inhabited α] [Inhabited β]
    (left : Slice α) (right : Slice β) (transform : α → β → α) (start : Nat) :
    (mapFrom left right transform start).length = left.length := by simp [mapFrom]

theorem mapFrom_word {α β : Type} [Inhabited α] [Inhabited β]
    (left : Slice α) (right : Slice β) (transform : α → β → α)
    (start i : Nat) (bound : i < left.length) :
    (mapFrom left right transform start)[i]! =
      if start ≤ i then transform left[i]! right[i]! else left[i]! := by
  simp only [mapFrom, Slice.getElem!_Nat_eq, Slice.from_val]
  rw [← List.Inhabited_getElem_eq_getElem! _ i (by simpa using bound), List.getElem_ofFn]

theorem mapFrom_full_length {α β : Type} [Inhabited α] [Inhabited β]
    (left : Slice α) (right : Slice β) (transform : α → β → α) :
    mapFrom left right transform left.length = left := by
  apply Slice.ext_getElem (mapFrom_length left right transform _)
  intro i mappedBound bound
  rw [Slice.Inhabited_getElem_eq_getElem! _ i mappedBound, Slice.Inhabited_getElem_eq_getElem! left i bound,
    mapFrom_word left right transform _ i bound, ite_eq_right (by omega)]

theorem apply_step {α β : Type} [Inhabited α] [Inhabited β]
    (left : Slice α) (right : Slice β) (transform : α → β → α)
    (i : Nat) (bound : i < left.length) :
    replaceLeft (stateAt (mapFrom left right transform (i + 1)) right left.length)
        i (transform left[i]! right[i]!) =
      stateAt (mapFrom left right transform i) right left.length := by
  have update : (mapFrom left right transform (i + 1)).setAtNat i
        (transform left[i]! right[i]!) = mapFrom left right transform i := by
    apply Slice.ext_getElem (by simp)
    intro j updatedBound outputBound
    have jBound : j < left.length := by simpa using outputBound
    rw [Slice.Inhabited_getElem_eq_getElem! _ j updatedBound,
      Slice.Inhabited_getElem_eq_getElem! _ j outputBound,
      mapFrom_word left right transform _ j jBound]
    rw [Slice.getElem!_Nat_eq]
    by_cases same : i = j
    · subst j
      rw [Slice.getElem!_Nat_setAtNat_eq _ _ _ (by simpa using bound), ite_eq_left (by omega)]
    · rw [Slice.getElem!_Nat_setAtNat_ne _ _ _ _ same, ← Slice.getElem!_Nat_eq,
        mapFrom_word left right transform _ j jBound]
      have sameGuard : i + 1 ≤ j ↔ i ≤ j := by omega
      simp only [sameGuard]
  simp only [replaceLeft, stateAt, update]

/-- A source loop with these checked steps applies each pending backward update
once. The induction uses the number of pairs remaining in the forward scan. -/
theorem map_loop {α β : Type} [Inhabited α] [Inhabited β]
    (left : Slice α) (right : Slice β) (transform : α → β → α)
    (body : State α β × (State α β → State α β) →
      Result (ControlFlow (State α β × (State α β → State α β)) (State α β)))
    (step : ∀ i, i < left.length → ∀ back,
      body (stateAt left right i, back) =
        Result.ok (ControlFlow.cont (stateAt left right (i + 1),
          fun final => back (replaceLeft final i (transform left[i]! right[i]!)))))
    (done : ∀ back, body (stateAt left right left.length, back) =
      Result.ok (ControlFlow.done (back (stateAt left right left.length))))
    (start : Nat) (bound : start ≤ left.length) (back : State α β → State α β) :
    loop body (stateAt left right start, back) =
      Result.ok (back (stateAt (mapFrom left right transform start) right left.length)) := by
  suffices ∀ remaining start, start ≤ left.length → left.length - start = remaining →
    ∀ back : State α β → State α β,
      loop body (stateAt left right start, back) =
        Result.ok (back (stateAt (mapFrom left right transform start) right left.length))
    from this (left.length - start) start bound rfl back
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
    intro start bounded eq back
    by_cases active : start < left.length
    · have rest := ih (left.length - (start + 1)) (by omega) (start + 1) (by omega) rfl
        (fun final => back (replaceLeft final start (transform left[start]! right[start]!)))
      unfold loop
      rw [step start active back]
      simp only [bind_ok]
      rw [rest, apply_step left right transform start active]
    · have terminal : start = left.length := by omega
      subst start
      unfold loop
      simp only [done back, bind_ok, mapFrom_full_length]

end BulksketchBridge.MutableZip
