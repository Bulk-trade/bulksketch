import Arithmetic.AvxTileGenerated
import BulksketchBridge.MutableZip
import BulksketchBridge.AvxTileSyndrome

namespace BulksketchBridge.AvxTilePowerLoop

open Aeneas Aeneas.Std Result ControlFlow
open Aeneas.Std.Avx512Register Aeneas.Std.AvxTileRuntime
open BulksketchBridge.Avx512RegisterChallenges BulksketchBridge.AvxTileSyndrome
open bulksketch.backend.x86_vpclmul512

set_option maxHeartbeats 1500000

abbrev PowerState := BulksketchBridge.MutableZip.State Word512 Word512
abbrev Back := PowerState → PowerState
abbrev Output := Word512 × PowerState × Back

def active (state : PowerState) : Prop :=
  state.fst.i < state.fst.slice.length ∧ state.snd.i < state.snd.slice.length

local instance (state : PowerState) : Decidable (active state) := by
  unfold active
  infer_instance

def advance (state : PowerState) : PowerState :=
  ⟨{ state.fst with i := state.fst.i + 1 }, { state.snd with i := state.snd.i + 1 }⟩

def product (state : PowerState) : Word512 :=
  productsReduced state.fst.slice[state.fst.i]! state.snd.slice[state.snd.i]!

theorem power_body_active (CL : Bool) (state : PowerState) (back : Back) (sum : Word512)
    (more : active state) :
    insert_tile_loop1_loop0.body CL state back sum =
      .ok (.cont (advance state, fun later => back
        (BulksketchBridge.MutableZip.replaceLeft later state.fst.i (product state)),
        xorRegister sum (product state))) := by
  have dispatch : AvxTileRuntime.zipNext (mutableWords Word512)
      (core.iter.traits.iterator.IteratorSliceIter Word512) state =
    bulksketch.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (bulksketch.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT Word512)
      (core.iter.traits.iterator.IteratorSliceIter Word512) state := rfl
  have next := BulksketchBridge.MutableZip.next_some state more.1 more.2
  rw [insert_tile_loop1_loop0.body, dispatch, next, bind_ok]
  dsimp! only
  simp only [bind_ok, xorWords, advance, product,
    Slice.Inhabited_getElem_eq_getElem! _ _ more.1, Slice.Inhabited_getElem_eq_getElem! _ _ more.2]
  have mul := Avx512Register.multiply_refines CL state.fst.slice[state.fst.i]! state.snd.slice[state.snd.i]!
  rw [mul, bind_ok]
  rfl

theorem power_body_done (CL : Bool) (state : PowerState) (back : Back) (sum : Word512)
    (done : ¬active state) :
    insert_tile_loop1_loop0.body CL state back sum = .ok (.done (sum, state, back)) := by
  have dispatch : AvxTileRuntime.zipNext (mutableWords Word512)
      (core.iter.traits.iterator.IteratorSliceIter Word512) state =
    bulksketch.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (bulksketch.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT Word512)
      (core.iter.traits.iterator.IteratorSliceIter Word512) state := rfl
  have exhausted : state.fst.slice.length ≤ state.fst.i ∨ state.snd.slice.length ≤ state.snd.i := by
    unfold active at done
    omega
  rw [insert_tile_loop1_loop0.body, dispatch, BulksketchBridge.MutableZip.next_done state exhausted, bind_ok]
  rfl

private def remaining (state : PowerState) : Nat := state.fst.slice.length - state.fst.i

/-- Each pair advances its power by the corresponding square. The aggregate
is the XOR fold over the new powers. Source callbacks compose in loop order. -/
def powerWrites : Nat → PowerState → Back → Word512 → Output
  | 0, state, back, sum => (sum, state, back)
  | fuel + 1, state, back, sum =>
    if active state then
      powerWrites fuel (advance state)
        (fun later => back (BulksketchBridge.MutableZip.replaceLeft later state.fst.i (product state)))
        (xorRegister sum (product state))
    else (sum, state, back)

theorem power_loop_refines (CL : Bool) (state : PowerState) (back : Back) (sum : Word512) :
    insert_tile_loop1_loop0 CL state back sum = .ok (powerWrites (remaining state) state back sum) := by
  suffices ∀ fuel state, remaining state = fuel → ∀ back sum,
    insert_tile_loop1_loop0 CL state back sum = .ok (powerWrites fuel state back sum) from
    this (remaining state) state rfl back sum
  intro fuel
  induction fuel with
  | zero =>
    intro state empty back sum
    have done : ¬ active state := by
      intro more
      have first := more.1
      unfold remaining at empty
      omega
    conv_lhs => unfold insert_tile_loop1_loop0 loop
    dsimp only
    rw [power_body_done CL state back sum done, bind_ok]
    rfl
  | succ fuel ih =>
    intro state count back sum
    by_cases more : active state
    · have cursor : remaining (advance state) = fuel := by
        unfold remaining at count ⊢
        simp only [advance]
        omega
      conv_lhs => unfold insert_tile_loop1_loop0 loop
      dsimp only
      rw [power_body_active CL state back sum more, bind_ok]
      change insert_tile_loop1_loop0 CL (advance state) _ _ = _
      rw [ih (advance state) cursor]
      simp only [powerWrites, ite_eq_left more]
    · conv_lhs => unfold insert_tile_loop1_loop0 loop
      dsimp only
      rw [power_body_done CL state back sum more, bind_ok]
      simp only [powerWrites, ite_eq_right more]

#print axioms power_body_active
#print axioms power_body_done
#print axioms power_loop_refines

end BulksketchBridge.AvxTilePowerLoop
