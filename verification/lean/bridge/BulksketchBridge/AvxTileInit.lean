import Arithmetic.AvxTileGenerated
import BulksketchBridge.AvxSquareRows

namespace BulksketchBridge.AvxTileInit

open Aeneas Aeneas.Std Result ControlFlow
open Aeneas.Std.Avx512Register Aeneas.Std.AvxTileRuntime Aeneas.Std.AvxHornerChunkRuntime
open BulksketchBridge.AvxTileDoubleZip BulksketchBridge.Avx512RegisterChallenges
open bulksketch.backend.x86_vpclmul512

set_option maxHeartbeats 1300000

abbrev Back := Init → Init

def active (state : Init) : Prop :=
  state.fst.fst.i < state.fst.fst.slice.length ∧
    state.fst.snd.i < state.fst.snd.slice.length ∧ state.snd.offset < state.snd.words.length

def stop (state : Init) : Nat := min (state.snd.offset + state.snd.width) state.snd.words.length

def chunk (state : Init) : Slice U64 := window state.snd.words state.snd.offset (stop state)

def advance (state : Init) : Init :=
  ⟨⟨{ state.fst.fst with i := state.fst.fst.i + 1 },
    { state.fst.snd with i := state.fst.snd.i + 1 }⟩,
    { state.snd with offset := stop state }⟩

def writePower (state later : Init) (power : Word512) : Init :=
  ⟨⟨overwrite state.fst.fst.i later.fst.fst (some power), later.fst.snd⟩, later.snd⟩

def writeStep (state later : Init) (step : Word512) : Init :=
  ⟨⟨later.fst.fst, overwrite state.fst.snd.i later.fst.snd (some step)⟩, later.snd⟩

theorem chunk_width (state : Init) (width : state.snd.width ≤ 8) :
    (chunk state).length ≤ 8 := by
  unfold chunk window stop
  simp only [Slice.from_val, Slice.length, List.slice, List.length_take, List.length_drop]
  omega

theorem init_body_active (load : AvxSquareRuntime.Load) (law : AvxSquare.LoadLaw load)
    (CL : Bool) (state : Init) (backStep backPower : Back)
    (more : active state) (width : state.snd.width ≤ 8) :
    insert_tile_loop0.body load CL state backStep backPower =
      .ok (.cont (advance state,
        fun later => backStep (writeStep state later
          (productsReduced (AvxSquare.loadWords (chunk state)) (AvxSquare.loadWords (chunk state)))),
        fun later => backPower (writePower state later (AvxSquare.loadWords (chunk state))))) := by
  have loadExact := law (chunk state) (chunk_width state width)
  have product := Avx512Register.multiply_refines CL
    (AvxSquare.loadWords (chunk state)) (AvxSquare.loadWords (chunk state))
  have nextPair := next_both_active state.fst more.1 more.2.1
  have dispatch : AvxTileRuntime.zipNext (bothMutableWords (mutableWords Word512)
      (mutableWords Word512)) (chunkWords U64) state = nextInit state := rfl
  unfold active at more
  rw [insert_tile_loop0.body, dispatch, nextInit, ite_eq_left more, nextPair]
  simp only [nextShared, ite_eq_left more.2.2, bind_ok]
  dsimp! only
  simp only [bind_ok]
  dsimp! only
  rw [show window state.snd.words state.snd.offset
    (min (state.snd.offset + state.snd.width) state.snd.words.length) = chunk state from rfl,
    loadExact, bind_ok, product, bind_ok]
  rfl

theorem init_body_done (load : AvxSquareRuntime.Load) (CL : Bool) (state : Init)
    (backStep backPower : Back) (done : ¬ active state) :
    insert_tile_loop0.body load CL state backStep backPower =
      .ok (.done (backStep state, backPower state)) := by
  have dispatch : AvxTileRuntime.zipNext (bothMutableWords (mutableWords Word512)
      (mutableWords Word512)) (chunkWords U64) state = nextInit state := rfl
  unfold active at done
  rw [insert_tile_loop0.body, dispatch, nextInit, ite_eq_right done, bind_ok]
  rfl

#print axioms init_body_active
#print axioms init_body_done

end BulksketchBridge.AvxTileInit
