import Arithmetic.AvxSliceKernelGenerated
import BulksketchBridge.AvxHornerInner
import BulksketchBridge.AvxSquareRows

namespace BulksketchBridge.AvxSliceKernel

open Aeneas Aeneas.Std Result ControlFlow
open Aeneas.Std.AvxSquareRuntime Aeneas.Std.Avx512Register
open Aeneas.Std.AvxHornerChunkRuntime
open BulksketchBridge.Avx512RegisterChallenges AvxSquare
open bulksketch.backend.x86_vpclmul512

set_option maxRecDepth 4096
set_option maxHeartbeats 2200000

abbrev PairState := AvxSliceKernelRuntime.State U64 U64
abbrev Back := PairState → PairState

inductive Kernel where
  | square
  | scale (factor : Word512)

abbrev broadcastWord := AvxHorner.splat

def pairAt (dst src : Slice U64) (dstOffset srcOffset : Nat) : PairState :=
  ⟨⟨dst, dstOffset, 8⟩, ⟨src, srcOffset, 8⟩⟩

def active (state : PairState) : Prop :=
  state.fst.offset < state.fst.words.length ∧ state.snd.offset < state.snd.words.length

local instance (state : PairState) : Decidable (active state) := by
  unfold active
  infer_instance

def chunkStop (state : ChunkState U64) : Nat := min (state.offset + state.width) state.words.length

def chunk (state : ChunkState U64) : Slice U64 := window state.words state.offset (chunkStop state)

def nextPair (state : PairState) : PairState :=
  ⟨{ state.fst with offset := chunkStop state.fst }, { state.snd with offset := chunkStop state.snd }⟩

def putChunk (state later : PairState) (written : Slice U64) : PairState :=
  ⟨{ later.fst with words := later.fst.words.setSlice! state.fst.offset written.val }, later.snd⟩

def register (kernel : Kernel) (dst src : Slice U64) : Word512 :=
  match kernel with
  | .square => productsReduced (loadWords src) (loadWords src)
  | .scale factor => fun pair high =>
    loadWords dst pair high ^^^ productsReduced (loadWords src) factor pair high

theorem chunk_length (state : ChunkState U64) : (chunk state).length ≤ state.width := by
  unfold chunk window chunkStop
  simp only [Slice.length, Slice.from_val, List.slice, List.length_take, List.length_drop]
  omega

def blockWords (kernel : Kernel) (state : PairState) : Slice U64 :=
  let dst := chunk state.fst
  if room : dst.length ≤ 8 then
    storeWords dst (register kernel dst (chunk state.snd)) room
  else dst

def body (load : Load) (store : Store) (kernel : Kernel) (CL : Bool) :
    PairState → Back → Result (ControlFlow (PairState × Back) PairState) :=
  match kernel with
  | .square => square_kernel_loop.body load store CL
  | .scale factor => scale_kernel_loop.body load store CL factor

def run (load : Load) (store : Store) (kernel : Kernel) (CL : Bool) :
    PairState → Back → Result PairState :=
  match kernel with
  | .square => square_kernel_loop load store CL
  | .scale factor => fun state back => scale_kernel_loop load store CL state back factor

private theorem next_active (state : PairState) (more : active state) :
    AvxSliceKernelRuntime.zipNext nextMutable nextShared state =
      .ok (some (chunk state.fst, chunk state.snd), nextPair state,
        fun later replacement => match replacement with
          | none => later
          | some words => putChunk state later words.1) := by
  unfold active at more
  rw [AvxSliceKernelRuntime.zipNext, ite_eq_left more]
  simp only [nextMutable, nextShared, ite_eq_left more.1, ite_eq_left more.2, bind_ok]
  dsimp! only
  simp only [bind_ok]
  dsimp! only
  congr 3
  funext later replacement
  cases replacement <;> cases later <;> rfl

private theorem next_done (state : PairState) (done : ¬active state) :
    AvxSliceKernelRuntime.zipNext nextMutable nextShared state =
      .ok (none, state, fun later _ => later) := by
  unfold active at done
  rw [AvxSliceKernelRuntime.zipNext, ite_eq_right done]

theorem body_active (load : Load) (store : Store) (loadLaw : LoadLaw load) (storeLaw : StoreLaw store)
    (kernel : Kernel) (CL : Bool) (state : PairState) (back : Back)
    (dstWidth : state.fst.width ≤ 8) (srcWidth : state.snd.width ≤ 8) (more : active state) :
    body load store kernel CL state back =
      .ok (.cont (nextPair state, fun later => back (putChunk state later (blockWords kernel state)))) := by
  have dst := (chunk_length state.fst).trans dstWidth
  have src := (chunk_length state.snd).trans srcWidth
  have readSrc := loadLaw (chunk state.snd) src
  have readDst := loadLaw (chunk state.fst) dst
  have write := storeLaw (chunk state.fst) (register kernel (chunk state.fst) (chunk state.snd)) dst
  have next := next_active state more
  cases kernel with
  | square =>
    have mul := Avx512Register.multiply_refines CL (loadWords (chunk state.snd)) (loadWords (chunk state.snd))
    simp only [body, square_kernel_loop.body, next, bind_ok]
    dsimp! only
    rw [readSrc, bind_ok, mul, bind_ok]
    change Aeneas.Std.bind (store (chunk state.fst) (register .square (chunk state.fst) (chunk state.snd))) _ = _
    rw [write, bind_ok]
    simp only [blockWords, dite_eq_left dst]
  | scale factor =>
    have mul := Avx512Register.multiply_refines CL (loadWords (chunk state.snd)) factor
    simp only [body, scale_kernel_loop.body, next, bind_ok]
    dsimp! only
    rw [readDst, bind_ok, readSrc, bind_ok, mul, bind_ok, xorWords, bind_ok]
    change Aeneas.Std.bind (store (chunk state.fst) (register (.scale factor) (chunk state.fst) (chunk state.snd))) _ = _
    rw [write, bind_ok]
    simp only [blockWords, dite_eq_left dst]

theorem body_done (load : Load) (store : Store) (kernel : Kernel) (CL : Bool) (state : PairState)
    (back : Back) (done : ¬active state) :
    body load store kernel CL state back = .ok (.done (back state)) := by
  have next := next_done state done
  cases kernel <;> simp only [body, scale_kernel_loop.body, square_kernel_loop.body, next, bind_ok] <;> rfl

private theorem unfold_run (load : Load) (store : Store) (kernel : Kernel) (CL : Bool) (state : PairState)
    (back : Back) :
    run load store kernel CL state back = (do
      let action ← body load store kernel CL state back
      match action with
      | .done output => .ok output
      | .cont next => run load store kernel CL next.1 next.2) := by
  cases kernel with
  | square =>
    conv_lhs => unfold run square_kernel_loop loop
    simp only [body, run, square_kernel_loop]
    apply congrArg (Aeneas.Std.bind (square_kernel_loop.body load store CL state back))
    funext action
    cases action with
    | cont state => cases state; rfl
    | done _ => rfl
  | scale factor =>
    conv_lhs => unfold run scale_kernel_loop loop
    simp only [body, run, scale_kernel_loop]
    apply congrArg (Aeneas.Std.bind (scale_kernel_loop.body load store CL factor state back))
    funext action
    cases action with
    | cont state => cases state; rfl
    | done _ => rfl

/-- Exact finite fold of the original chunk pairs, including unequal
destination and source lengths and truncated final loads/stores. -/
noncomputable def model (kernel : Kernel) : Nat → PairState → PairState
  | 0, state => state
  | fuel + 1, state =>
    if active state then putChunk state (model kernel fuel (nextPair state)) (blockWords kernel state)
    else state

theorem run_refines (load : Load) (store : Store) (loadLaw : LoadLaw load) (storeLaw : StoreLaw store)
    (kernel : Kernel) (CL : Bool) (fuel : Nat) (state : PairState) (back : Back)
    (width : state.fst.width = 8) (srcWidth : state.snd.width = 8)
    (enough : state.fst.words.length - state.fst.offset ≤ fuel) :
    run load store kernel CL state back = .ok (back (model kernel fuel state)) := by
  induction fuel generalizing state back with
  | zero =>
    have done : ¬active state := fun more => by have := more.1; omega
    rw [unfold_run, body_done _ _ _ _ _ _ done, bind_ok, model]
  | succ fuel ih =>
    by_cases more : active state
    · have progress : state.fst.offset < (nextPair state).fst.offset := by
        have := more.1
        simp only [nextPair, chunkStop, width]
        omega
      have bound : (nextPair state).fst.words.length - (nextPair state).fst.offset ≤ fuel := by
        change state.fst.words.length - (nextPair state).fst.offset ≤ _
        omega
      rw [unfold_run, body_active load store loadLaw storeLaw kernel CL state back (by omega) (by omega) more,
        bind_ok]
      dsimp! only
      rw [ih (nextPair state) _ width srcWidth bound]
      simp only [model, ite_eq_left more]
    · rw [unfold_run, body_done _ _ _ _ _ _ more, bind_ok]
      simp only [model, ite_eq_right more]

/-- The original square kernel preserves exact short-tail and untouched
destination behavior for every pair of slice lengths. -/
def ActualAvxSquareKernel : Prop :=
  ∀ (load : Load) (store : Store), LoadLaw load → StoreLaw store →
    ∀ CL dst src,
      square_kernel load store CL dst src =
        .ok ((model .square dst.length (pairAt dst src 0 0)).fst.words)

theorem square_kernel_refines : ActualAvxSquareKernel := by
  intro load store loadLaw storeLaw CL dst src
  have scan := run_refines load store loadLaw storeLaw .square CL dst.length
    (pairAt dst src 0 0) id rfl rfl (by simp [pairAt])
  unfold square_kernel
  simp only [chunksMut, chunks, bind_ok, AvxSliceKernelRuntime.zipConstruct,
    show (8#usize).val ≠ 0 from by decide, ite_false]
  dsimp! only
  change Aeneas.Std.bind (run load store .square CL (pairAt dst src 0 0) id) _ = _
  rw [scan, bind_ok]
  rfl

def ActualAvxScaleKernel : Prop :=
  ∀ (load : Load) (store : Store) (xor : AvxSliceKernelRuntime.Xor),
    LoadLaw load → StoreLaw store → ∀ CL dst src scale,
      scale_kernel load store xor CL dst src scale =
        if scale = 0#u64 then .ok dst
        else if scale = 1#u64 then xor dst src
        else .ok ((model (.scale (broadcastWord scale)) dst.length (pairAt dst src 0 0)).fst.words)

theorem scale_kernel_refines : ActualAvxScaleKernel := by
  intro load store xor loadLaw storeLaw CL dst src scale
  by_cases zero : scale = 0#u64
  · simp only [scale_kernel, zero, ite_true]
  · by_cases one : scale = 1#u64
    · simp only [scale_kernel, zero, one, ite_false, ite_true]
    · have scan := run_refines load store loadLaw storeLaw (.scale (broadcastWord scale)) CL dst.length
        (pairAt dst src 0 0) id rfl rfl (by simp [pairAt])
      have exactBroadcast :
          broadcast (core.num.I64.from_le_bytes (core.num.U64.to_le_bytes scale)) =
            .ok (broadcastWord scale) := by
        simpa only [X86PclmulRuntime.unsignedBytes, X86PclmulRuntime.signedFromBytes, bind_ok,
          broadcastWord] using AvxHorner.broadcast_normal scale
      unfold scale_kernel
      simp only [zero, one, ite_false, X86PclmulRuntime.unsignedBytes,
        X86PclmulRuntime.signedFromBytes, exactBroadcast, bind_ok, chunksMut, chunks,
        AvxSliceKernelRuntime.zipConstruct, show (8#usize).val ≠ 0 from by decide]
      dsimp! only
      change Aeneas.Std.bind (run load store (.scale (broadcastWord scale)) CL (pairAt dst src 0 0) id) _ = _
      rw [scan, bind_ok]
      rfl

#print axioms square_kernel_refines
#print axioms scale_kernel_refines

end BulksketchBridge.AvxSliceKernel
