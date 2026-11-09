import BulksketchBridge.AvxSliceKernel
import BulksketchBridge.AvxSquareWindows

namespace BulksketchBridge.AvxSliceKernel

open Aeneas Aeneas.Std Algebra.Gf64
open Aeneas.Std.Avx512Register
open AvxSquare X86MaskedMemory
open BulksketchBridge.Avx512RegisterChallenges

set_option maxRecDepth 4096
set_option maxHeartbeats 2600000

inductive Operation where
  | square
  | scale (factor : U64)

def Operation.kernel : Operation → Kernel
  | .square => .square
  | .scale factor => .scale (broadcastWord factor)

def Operation.word : Operation → U64 → U64 → U64
  | .square => fun _ src => ⟨multiplyWord src.bv src.bv⟩
  | .scale factor => fun dst src => dst ^^^ ⟨multiplyWord src.bv factor.bv⟩

def stopAt (dst : Slice U64) (offset : Nat) : Nat := min (offset + 8) dst.length

def evalFrom (op : Operation) (dst src : Slice U64) (offset : Nat) : Slice U64 :=
  Slice.from (List.ofFn fun i : Fin dst.length =>
    if offset ≤ i.val then op.word dst[i.val]! src[i.val]! else dst[i.val]!)
    (by simp)

@[simp] theorem eval_length (op : Operation) (dst src : Slice U64) (offset : Nat) :
    (evalFrom op dst src offset).length = dst.length := by simp [evalFrom, Slice.length]

theorem eval_word (op : Operation) (dst src : Slice U64) (offset i : Nat) (inside : i < dst.length) :
    (evalFrom op dst src offset)[i]! =
      if offset ≤ i then op.word dst[i]! src[i]! else dst[i]! := by
  simp only [evalFrom, Slice.getElem!_Nat_eq, Slice.from_val]
  rw [← List.Inhabited_getElem_eq_getElem! _ i (by simpa using inside), List.getElem_ofFn]

private theorem register_lane (op : Operation) (dst src : Slice U64) (lane : Fin 8)
    (dstRoom : lane.val < dst.length) (srcRoom : lane.val < src.length) :
    flatten (register op.kernel dst src) lane = (op.word dst[lane.val]! src[lane.val]!).bv := by
  have idx : flatIndex ⟨lane.val / 2, by omega⟩ (decide (lane.val % 2 = 1)) = lane := by
    apply Fin.ext
    simp only [flatIndex, decide_eq_true_eq]
    split <;> omega
  cases op with
  | square =>
    simp only [Operation.kernel, register, flatten, productsReduced, loadWords,
      idx, ite_eq_left srcRoom, Operation.word]
  | scale factor =>
    simp only [Operation.kernel, register, flatten, productsReduced, loadWords,
      idx, ite_eq_left srcRoom, ite_eq_left dstRoom, Operation.word, AvxHorner.splat]
    rfl

theorem block_words_len (op : Operation) (dst src : Slice U64) (offset : Nat) :
    (blockWords op.kernel (pairAt dst src offset offset)).length = stopAt dst offset - offset := by
  let stop := stopAt dst offset
  have bound : stop ≤ dst.length := Nat.min_le_right _ _
  have rangeLen : (ClosedLeaf.region dst offset stop).length = stop - offset :=
    ClosedLeaf.region_length _ _ _ bound
  have width : stop - offset ≤ 8 := by unfold stop stopAt; omega
  unfold blockWords
  change (if h : (ClosedLeaf.region dst offset stop).length ≤ 8 then
    (storeWords (ClosedLeaf.region dst offset stop)
      (register op.kernel (ClosedLeaf.region dst offset stop) (chunk (pairAt dst src offset offset).snd)) h)
    else ClosedLeaf.region dst offset stop).length = _
  rw [dite_eq_left (rangeLen.trans_le width)]
  simp only [storeWords, registerPayload, Slice.length, Slice.from_val, List.length_map, List.length_ofFn]
  exact rangeLen

theorem block_word (op : Operation) (dst src : Slice U64) (same : dst.length = src.length)
    (offset lane : Nat) (inside : offset + lane < stopAt dst offset) :
    (blockWords op.kernel (pairAt dst src offset offset))[lane]! =
      op.word dst[offset + lane]! src[offset + lane]! := by
  let stop := stopAt dst offset
  have dstBound : stop ≤ dst.length := Nat.min_le_right _ _
  have srcBound : stop ≤ src.length := dstBound.trans_eq same
  have width : stop - offset ≤ 8 := by unfold stop stopAt; omega
  have exactDst : chunk (pairAt dst src offset offset).fst = ClosedLeaf.region dst offset stop := rfl
  have exactSrc : chunk (pairAt dst src offset offset).snd = ClosedLeaf.region src offset stop := by
    change ClosedLeaf.region src offset (stopAt src offset) = _
    simp only [stop, stopAt, same]
  have dstLen : (ClosedLeaf.region dst offset stop).length = stop - offset :=
    ClosedLeaf.region_length _ _ _ dstBound
  have srcLen : (ClosedLeaf.region src offset stop).length = stop - offset :=
    ClosedLeaf.region_length _ _ _ srcBound
  have fits : (ClosedLeaf.region dst offset stop).length ≤ 8 := by omega
  let ix : Fin 8 := ⟨lane, by omega⟩
  have read (words : Slice U64) (room : stop ≤ words.length) :
      (ClosedLeaf.region words offset stop)[lane]! = words[offset + lane]! := by
    simp only [ClosedLeaf.region, Slice.getElem!_Nat_eq, Slice.from_val]
    exact List.getElem!_slice offset stop lane words.val ⟨room, inside⟩
  have room : lane < (blockWords op.kernel (pairAt dst src offset offset)).length := by
    rw [block_words_len]
    omega
  apply U64.bv_eq_imp_eq
  rw [← Slice.Inhabited_getElem_eq_getElem! _ _ room, Slice.getElem_Nat_eq _ _ (by exact room)]
  simp only [blockWords, exactDst, exactSrc, dite_eq_left fits, storeWords, registerPayload, Slice.from_val,
    List.getElem_map, List.getElem_ofFn]
  change flatten (register op.kernel (ClosedLeaf.region dst offset stop) (ClosedLeaf.region src offset stop)) ix = _
  rw [register_lane op _ _ ix (by change lane < _; omega) (by change lane < _; omega),
    read dst dstBound, read src srcBound]

private theorem put_eval (op : Operation) (dst src : Slice U64) (same : dst.length = src.length)
    (offset : Nat) (active : offset < dst.length) :
    (evalFrom op dst src (stopAt dst offset)).setSlice! offset
      (blockWords op.kernel (pairAt dst src offset offset)).val = evalFrom op dst src offset := by
  let stop := stopAt dst offset
  let values := blockWords op.kernel (pairAt dst src offset offset)
  have valueLen : values.length = stop - offset := block_words_len ..
  have progress : offset < stop := by unfold stop stopAt; omega
  apply Slice.ext_getElem (by simp)
  intro i left right
  have inside : i < dst.length := by simpa using right
  rw [Slice.Inhabited_getElem_eq_getElem! _ _ left, Slice.Inhabited_getElem_eq_getElem! _ _ right,
    eval_word op dst src offset i inside]
  by_cases before : i < offset
  · rw [Slice.setSlice!_getElem!_prefix _ _ _ _ before, eval_word op dst src _ _ inside,
      ite_eq_right (by omega : ¬stop ≤ i), ite_eq_right (by omega : ¬offset ≤ i)]
  · by_cases after : stop ≤ i
    · rw [Slice.setSlice!_getElem!_suffix _ _ _ _ (by change offset + values.length ≤ i; omega),
        eval_word op dst src _ _ inside, ite_eq_left after, ite_eq_left (by omega : offset ≤ i)]
    · rw [Slice.setSlice!_getElem!_middle _ _ _ _ (by
        change offset ≤ i ∧ i - offset < values.length ∧ i < (evalFrom op dst src stop).length
        rw [eval_length]
        omega), ← Slice.getElem!_Nat_eq, ite_eq_left (by omega : offset ≤ i)]
      change values[i - offset]! = _
      rw [block_word op dst src same offset (i - offset) (by omega),
        show offset + (i - offset) = i by omega]

private theorem eval_finished (op : Operation) (dst src : Slice U64) (offset : Nat)
    (endReached : dst.length ≤ offset) : evalFrom op dst src offset = dst := by
  apply Slice.ext_getElem (by simp)
  intro i left right
  rw [Slice.Inhabited_getElem_eq_getElem! _ _ left, Slice.Inhabited_getElem_eq_getElem! _ _ right,
    eval_word op dst src offset i right, ite_eq_right (by omega : ¬offset ≤ i)]

theorem model_words (op : Operation) (dst src : Slice U64) (same : dst.length = src.length)
    (offset fuel : Nat) (enough : dst.length - offset ≤ fuel) :
    (model op.kernel fuel (pairAt dst src offset offset)).fst.words = evalFrom op dst src offset := by
  induction fuel generalizing offset with
  | zero =>
    rw [model, eval_finished op dst src offset (by omega)]
    rfl
  | succ fuel ih =>
    by_cases active : offset < dst.length
    · let stop := stopAt dst offset
      have more : AvxSliceKernel.active (pairAt dst src offset offset) :=
        ⟨active, by change offset < src.length; omega⟩
      have next : nextPair (pairAt dst src offset offset) = pairAt dst src stop stop := by
        simp only [nextPair, pairAt, chunkStop, stop, stopAt, same]
      have progress : offset < stop := by unfold stop stopAt; omega
      rw [model, ite_eq_left more, next]
      change ((model op.kernel fuel (pairAt dst src stop stop)).fst.words).setSlice! offset
        (blockWords op.kernel (pairAt dst src offset offset)).val = _
      rw [ih stop (by omega), put_eval op dst src same offset active]
    · have stopped : ¬AvxSliceKernel.active (pairAt dst src offset offset) := fun more => active more.1
      rw [model, ite_eq_right stopped, eval_finished op dst src offset (by omega)]
      rfl

#print axioms model_words

end BulksketchBridge.AvxSliceKernel
