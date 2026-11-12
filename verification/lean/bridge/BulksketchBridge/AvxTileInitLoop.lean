import BulksketchBridge.AvxTileInit

namespace BulksketchBridge.AvxTileInit

open Aeneas Aeneas.Std Result ControlFlow
open Aeneas.Std.AvxTileRuntime
open BulksketchBridge.Avx512RegisterChallenges
open bulksketch.backend.x86_vpclmul512

set_option maxHeartbeats 1600000

local instance (state : Init) : Decidable (active state) := by
  unfold active
  infer_instance

def remaining (state : Init) : Nat :=
  state.fst.fst.slice.length - state.fst.fst.i

/-- Compute the final independent saved states of the two native
initialization callbacks. Every recursive step consumes a register slot,
and each backward write uses the state returned by its entire suffix. -/
noncomputable def initWrites : Nat → Init → Init × Init
  | 0, state => (state, state)
  | fuel + 1, state =>
    if active state then
      let (steps, powers) := initWrites fuel (advance state)
      let register := AvxSquare.loadWords (chunk state)
      (writeStep state steps (productsReduced register register), writePower state powers register)
    else (state, state)

theorem init_loop_refines (load : AvxSquareRuntime.Load) (law : AvxSquare.LoadLaw load)
    (CL : Bool) (state : Init) (backStep backPower : Back) (width : state.snd.width ≤ 8) :
    insert_tile_loop0 load CL state backStep backPower =
      .ok (backStep (initWrites (remaining state) state).1, backPower (initWrites (remaining state) state).2) := by
  suffices ∀ fuel state, remaining state = fuel → state.snd.width ≤ 8 → ∀ backStep backPower,
    insert_tile_loop0 load CL state backStep backPower =
      .ok (backStep (initWrites fuel state).1, backPower (initWrites fuel state).2) from
    this (remaining state) state rfl width backStep backPower
  intro fuel
  induction fuel with
  | zero =>
    intro state empty width backStep backPower
    have done : ¬ active state := by
      intro activeState
      have first := activeState.1
      unfold remaining at empty
      omega
    conv_lhs => unfold insert_tile_loop0 loop
    dsimp only
    rw [init_body_done load CL state backStep backPower done, bind_ok]
    rfl
  | succ fuel ih =>
    intro state count width backStep backPower
    by_cases more : active state
    · have cursor : remaining (advance state) = fuel := by
        unfold remaining at count ⊢
        simp only [advance]
        omega
      have afterWidth : (advance state).snd.width ≤ 8 := width
      conv_lhs => unfold insert_tile_loop0 loop
      dsimp only
      rw [init_body_active load law CL state backStep backPower more width, bind_ok]
      change insert_tile_loop0 load CL (advance state) _ _ = _
      rw [ih (advance state) cursor afterWidth]
      simp only [initWrites, ite_eq_left more]
    · conv_lhs => unfold insert_tile_loop0 loop
      dsimp only
      rw [init_body_done load CL state backStep backPower more, bind_ok]
      simp only [initWrites, ite_eq_right more]

#print axioms init_loop_refines

end BulksketchBridge.AvxTileInit
