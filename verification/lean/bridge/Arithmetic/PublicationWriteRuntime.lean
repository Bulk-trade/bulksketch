import Arithmetic.CanonicalizeGenerated
import Arithmetic.WorkScheduleRuntime
import Arithmetic.PublicationFrameGenerated

namespace Aeneas.Std.PublicationWriteRuntime

open Aeneas Aeneas.Std Result

/-- The width-two Rust Windows specialization visits in order and stops
immediately after the first failing predicate. The cursor and predicate
state are kept even when the original caller discards the cursor. -/
def scanAll {T C : Type} (callback : core.ops.function.FnMut C T Bool) :
    List T → C → Result (Bool × Nat)
  | [], _ => .ok (true, 0)
  | item :: rest, state => do
    let (accept, state') ← callback.call_mut state item
    if accept then
      let (later, consumed) ← scanAll callback rest state'
      .ok (later, consumed + 1)
    else .ok (false, 1)

def allWindows {C : Type} (_ : Unit) (callback : core.ops.function.FnMut C (Slice U64) Bool)
    (it : List (Slice U64)) (state : C) : Result (Bool × List (Slice U64)) := do
  let (accept, consumed) ← scanAll callback it state
  .ok (accept, it.drop consumed)

def first {T : Type} (words : Slice T) : Result (Option T) := .ok words.val.head?

def andThen {T U F : Type} (call : core.ops.function.FnOnce F T (Option U))
    (option : Option T) (callback : F) : Result (Option U) :=
  match option with
  | none => .ok none
  | some value => call.call_once callback value

def optionCmp {T : Type} (cmp : core.cmp.PartialEq T T) : core.cmp.PartialEq (Option T) (Option T) :=
  { eq := ExecutionDriverRuntime.optionEq cmp
    ne := fun left right => do
      let same ← ExecutionDriverRuntime.optionEq cmp left right
      .ok (!same) }

theorem all_windows_exact {C : Type} (callback : core.ops.function.FnMut C (Slice U64) Bool)
    (windows : List (Slice U64)) (state : C) (pred : Slice U64 → Bool)
    (law : ∀ item ∈ windows, callback.call_mut state item = .ok (pred item, state)) :
    ∃ consumed, allWindows () callback windows state = .ok (windows.all pred, windows.drop consumed) := by
  have trace : ∃ consumed, scanAll callback windows state = .ok (windows.all pred, consumed) := by
    induction windows with
    | nil => exact ⟨0, rfl⟩
    | cons item rest ih =>
      have step := law item (by simp)
      have tail := ih (fun member proof => law member (by simp [proof]))
      cases good : pred item with
      | false =>
        refine ⟨1, ?_⟩
        rw [scanAll, step, bind_ok]
        simp [good]
      | true =>
        obtain ⟨consumed, exact⟩ := tail
        refine ⟨consumed + 1, ?_⟩
        rw [scanAll, step, bind_ok]
        simp [good, exact, bind_ok]
  obtain ⟨consumed, exact⟩ := trace
  exact ⟨consumed, by simp [allWindows, exact, bind_ok]⟩

#print axioms all_windows_exact

end Aeneas.Std.PublicationWriteRuntime
