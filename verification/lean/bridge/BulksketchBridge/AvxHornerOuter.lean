import BulksketchBridge.AvxHornerInner

namespace BulksketchBridge.AvxHorner

open Aeneas Aeneas.Std Aeneas.Std.Avx512Register Aeneas.Std.AvxSquareRuntime
open Aeneas.Std.AvxHornerChunkRuntime
open AvxSquare PortableHornerChallenges X86MaskedMemory
open bulksketch.backend.x86_vpclmul512

set_option maxRecDepth 4096
set_option maxHeartbeats 1700000

abbrev State := ZipState U64 U64
abbrev Back := State → State

def stateAt (points out : Slice U64) (offset : Nat) : State :=
  ⟨⟨points, offset, 8⟩, ⟨out, offset, 8⟩⟩

def restoreChunk (state : State) (offset : Nat) (words : Slice U64) : State :=
  ⟨state.fst, { state.snd with words := state.snd.words.setSlice! offset words.val }⟩

def blockEnd (points : Slice U64) (offset : Nat) : Nat := min (offset + 8) points.length

def blockRegister (leading : U64) (rest points : Slice U64) (offset stop : Nat) : Word512 :=
  let lanes := loadWords (window points offset stop)
  rest.val.reverse.foldl (registerStep lanes) (splat leading)

def blockValues (leading : U64) (rest points out : Slice U64) (offset stop : Nat) : Slice U64 :=
  let target := window out offset stop
  if fits : target.length ≤ 8 then storeWords target (blockRegister leading rest points offset stop) fits
  else target

def evalFrom (leading : U64) (rest points out : Slice U64) (offset : Nat) : Slice U64 :=
  Slice.from (List.ofFn fun i : Fin out.length =>
    if offset ≤ i.val then rest.val.reverse.foldl (stepWord points[i.val]!) leading else out[i.val]!)
    (by simp)

@[simp] theorem eval_from_length (leading : U64) (rest points out : Slice U64) (offset : Nat) :
    (evalFrom leading rest points out offset).length = out.length := by
  simp [evalFrom, Slice.length]

private theorem window_length (words : Slice U64) (start stop : Nat) (room : stop ≤ words.length) :
    (window words start stop).length = stop - start := by
  simp only [window, Slice.length, Slice.from_val, List.slice_length]
  exact Nat.min_eq_right (Nat.sub_le_sub_right room start)

private theorem window_word (words : Slice U64) (start stop i : Nat)
    (room : stop ≤ words.length) (inside : start + i < stop) :
    (window words start stop)[i]! = words[start + i]! := by
  simp only [window, Slice.getElem!_Nat_eq, Slice.from_val]
  exact List.getElem!_slice start stop i words.val ⟨room, inside⟩

private theorem store_length (words : Slice U64) (value : Word512) (bound : words.length ≤ 8) :
    (storeWords words value bound).length = words.length := by
  simp [storeWords, registerPayload, Slice.length]

private theorem store_word (words : Slice U64) (value : Word512) (bound : words.length ≤ 8)
    (slot : Nat) (active : slot < words.length) :
    (storeWords words value bound)[slot]!.bv = flatten value ⟨slot, by omega⟩ := by
  have length := store_length words value bound
  rw [← Slice.Inhabited_getElem_eq_getElem! _ _ (by omega : slot < (storeWords words value bound).length)]
  rw [Slice.getElem_Nat_eq]
  simp only [storeWords, registerPayload, Slice.from_val, List.getElem_map, List.getElem_ofFn]
  change slot < (storeWords words value bound).length
  omega

theorem block_values_length (leading : U64) (rest points out : Slice U64) (offset stop : Nat)
    (room : stop ≤ out.length) (width : stop - offset ≤ 8) :
    (blockValues leading rest points out offset stop).length = stop - offset := by
  have exactWidth := window_length out offset stop room
  unfold blockValues
  rw [dite_eq_left (show (window out offset stop).length ≤ 8 by omega), store_length, exactWidth]

theorem block_value_word (leading : U64) (rest points out : Slice U64) (offset stop i : Nat)
    (pointRoom : stop ≤ points.length) (outRoom : stop ≤ out.length)
    (width : stop - offset ≤ 8) (inside : offset + i < stop) :
    (blockValues leading rest points out offset stop)[i]! =
      rest.val.reverse.foldl (stepWord points[offset + i]!) leading := by
  have targetLen := window_length out offset stop outRoom
  have pointLen := window_length points offset stop pointRoom
  have bound : (window out offset stop).length ≤ 8 := by omega
  have active : i < (window out offset stop).length := by omega
  have activePoint : i < (window points offset stop).length := by omega
  unfold blockValues
  rw [dite_eq_left bound]
  apply U64.bv_eq_imp_eq
  let lane : Fin 8 := ⟨i, by omega⟩
  trans flatten (blockRegister leading rest points offset stop) lane
  · exact store_word (window out offset stop) (blockRegister leading rest points offset stop) bound i active
  have same : flatIndex ⟨lane.val / 2, by have := lane.isLt; omega⟩ (decide (lane.val % 2 = 1)) = lane := by
    apply Fin.ext
    simp only [flatIndex, decide_eq_true_eq]
    split <;> omega
  change flatten (blockRegister leading rest points offset stop) lane = _
  unfold flatten blockRegister
  rw [lane_fold]
  have indexEq : (flatIndex ⟨i / 2, by omega⟩ (decide (i % 2 = 1))).val = i :=
    congrArg Fin.val same
  simp only [loadWords, show lane.val = i from rfl, indexEq, activePoint, ite_true,
    window_word points offset stop i pointRoom inside, splat]

private theorem zip_active (points out : Slice U64) (offset : Nat)
    (same : out.length = points.length) (active : offset < points.length) :
    zipNext nextShared nextMutable (stateAt points out offset) =
      .ok (some (window points offset (blockEnd points offset), window out offset (blockEnd points offset)),
        stateAt points out (blockEnd points offset),
        fun later replacement => match replacement with
          | none => later
          | some items => restoreChunk later offset items.2) := by
  simp only [zipNext, stateAt, active, and_self, ite_true, nextShared, nextMutable, bind_ok,
    same, blockEnd]
  dsimp! only
  simp only [bind_ok]
  dsimp! only
  congr 3
  funext later replacement
  cases replacement <;> cases later <;> rfl

private theorem zip_done (points out : Slice U64) (offset : Nat) (inactive : points.length ≤ offset) :
    zipNext nextShared nextMutable (stateAt points out offset) =
      .ok (none, stateAt points out offset, fun later _ => later) := by
  simp only [zipNext, stateAt, show ¬offset < points.length from Nat.not_lt.mpr inactive,
    false_and, ite_false]

private theorem block_body (loadModel : Load) (storeModel : Store)
    (loadLaw : LoadLaw loadModel) (storeLaw : StoreLaw storeModel)
    (cl : Bool) (leading : U64) (rest points out : Slice U64) (offset : Nat) (back : Back)
    (same : out.length = points.length) (active : offset < points.length) :
    horner_kernel_loop0.body loadModel storeModel cl leading rest (stateAt points out offset) back =
      .ok (.cont (stateAt points out (blockEnd points offset),
        fun later => back (restoreChunk later offset (blockValues leading rest points out offset (blockEnd points offset))))) := by
  let stop := blockEnd points offset
  have room : stop ≤ points.length := Nat.min_le_right _ _
  have width : stop - offset ≤ 8 := by unfold stop blockEnd; omega
  have pointWidth := window_length points offset stop room
  have outWidth := window_length out offset stop (by omega)
  have pointFit : (window points offset stop).length ≤ 8 := by omega
  have outFit : (window out offset stop).length ≤ 8 := by omega
  have load := loadLaw (window points offset stop) pointFit
  have store := storeLaw (window out offset stop) (blockRegister leading rest points offset stop) outFit
  have inner := inner_loop cl (loadWords (window points offset stop)) (splat leading) rest
  simp only [horner_kernel_loop0.body, zip_active points out offset same active, bind_ok]
  dsimp! only
  simp only [show blockEnd points offset = stop from rfl, load, bind_ok,
    X86PclmulRuntime.unsignedBytes, X86PclmulRuntime.signedFromBytes, broadcast,
    core.slice.Slice.iter, core.iter.traits.iterator.Iterator.rev.trait_default,
    core.iter.traits.iterator.Iterator.rev.default]
  have exactBroadcast := broadcast_normal leading
  simp only [X86PclmulRuntime.unsignedBytes, X86PclmulRuntime.signedFromBytes, broadcast, bind_ok] at exactBroadcast
  have broadcastValue := Result.ok_injective exactBroadcast
  simp only [broadcastValue, show (⟨⟨rest, 0⟩⟩ : Reverse) = reverseAt rest by rfl, inner, bind_ok]
  change (do
    let stored ← storeModel (window out offset stop) (blockRegister leading rest points offset stop)
    Result.ok (ControlFlow.cont (stateAt points out stop, fun later => back (restoreChunk later offset stored)))) = _
  simp only [Bind.bind, store, bind_ok, blockValues, dite_eq_left outFit]

theorem eval_from_word (leading : U64) (rest points out : Slice U64) (offset index : Nat)
    (active : index < out.length) :
    (evalFrom leading rest points out offset)[index]! =
      if offset ≤ index then rest.val.reverse.foldl (stepWord points[index]!) leading else out[index]! := by
  simp only [evalFrom, Slice.getElem!_Nat_eq, Slice.from_val]
  rw [← List.Inhabited_getElem_eq_getElem! _ index (by simpa using active), List.getElem_ofFn]

private theorem apply_block (leading : U64) (rest points out : Slice U64) (offset : Nat)
    (same : out.length = points.length) (active : offset < points.length) :
    (evalFrom leading rest points out (blockEnd points offset)).setSlice! offset
      (blockValues leading rest points out offset (blockEnd points offset)).val =
      evalFrom leading rest points out offset := by
  let stop := blockEnd points offset
  have room : stop ≤ points.length := Nat.min_le_right _ _
  have roomOut : stop ≤ out.length := by omega
  have less : offset < stop := by unfold stop blockEnd; omega
  have width : stop - offset ≤ 8 := by unfold stop blockEnd; omega
  let values := blockValues leading rest points out offset stop
  have valuesLen : values.length = stop - offset := block_values_length _ _ _ _ _ _ roomOut width
  let later := evalFrom leading rest points out stop
  apply Slice.ext_getElem (by simp)
  intro i b0 b1
  have bounded : i < out.length := by simpa using b1
  rw [Slice.Inhabited_getElem_eq_getElem! _ _ b0, Slice.Inhabited_getElem_eq_getElem! _ _ b1,
    eval_from_word _ _ _ _ _ _ bounded]
  change (later.setSlice! offset values.val)[i]! = _
  by_cases before : i < offset
  · rw [Slice.setSlice!_getElem!_prefix _ _ _ _ before]
    simp only [later, eval_from_word _ _ _ _ _ _ bounded, ite_eq_right (by omega : ¬stop ≤ i),
      ite_eq_right (by omega : ¬offset ≤ i)]
  · by_cases after : stop ≤ i
    · rw [Slice.setSlice!_getElem!_suffix _ _ _ _ (by change offset + values.length ≤ i; omega)]
      simp only [later, eval_from_word _ _ _ _ _ _ bounded, after, ite_true, show offset ≤ i by omega]
    · rw [Slice.setSlice!_getElem!_middle later values.val offset i (by
        change offset ≤ i ∧ i - offset < values.length ∧ i < later.length
        rw [eval_from_length]; omega),
        ← Slice.getElem!_Nat_eq, ite_eq_left (by omega : offset ≤ i)]
      change (blockValues leading rest points out offset stop)[i - offset]! = _
      rw [block_value_word _ _ _ _ _ _ _ room roomOut width (by omega),
        show offset + (i - offset) = i by omega]

/-- Every generated outer block composes the inner register fold with the
actual saved destination chunk continuation. -/
theorem outer_loop (loadModel : Load) (storeModel : Store)
    (loadLaw : LoadLaw loadModel) (storeLaw : StoreLaw storeModel)
    (cl : Bool) (leading : U64) (rest points out : Slice U64) (offset : Nat) (back : Back)
    (same : out.length = points.length) (bound : offset ≤ points.length) :
    horner_kernel_loop0 loadModel storeModel cl (stateAt points out offset) back leading rest =
      .ok (back (stateAt points (evalFrom leading rest points out offset) points.length)) := by
  suffices ∀ count offset, offset ≤ points.length → points.length - offset = count →
      ∀ back : Back,
        horner_kernel_loop0 loadModel storeModel cl (stateAt points out offset) back leading rest =
          .ok (back (stateAt points (evalFrom leading rest points out offset) points.length)) from
    this (points.length - offset) offset bound rfl back
  intro count
  induction count using Nat.strong_induction_on with
  | h count ih =>
    intro offset bound exactCount back
    by_cases active : offset < points.length
    · have step := block_body loadModel storeModel loadLaw storeLaw cl leading rest points out offset back same active
      have progress : offset < blockEnd points offset := by unfold blockEnd; omega
      have stopBound : blockEnd points offset ≤ points.length := Nat.min_le_right _ _
      have patch := apply_block leading rest points out offset same active
      conv_lhs => unfold horner_kernel_loop0 loop
      dsimp only
      rw [step, bind_ok]
      change horner_kernel_loop0 loadModel storeModel cl (stateAt points out (blockEnd points offset))
        (fun later => back (restoreChunk later offset (blockValues leading rest points out offset (blockEnd points offset))))
        leading rest = _
      rw [ih (points.length - blockEnd points offset) (by omega) (blockEnd points offset) stopBound rfl]
      simp only [restoreChunk, stateAt, patch]
    · have finished : offset = points.length := by omega
      subst offset
      have terminalOutput : evalFrom leading rest points out points.length = out := by
        apply Slice.ext_getElem (eval_from_length ..)
        intro i evalBound outBound
        rw [Slice.Inhabited_getElem_eq_getElem! _ _ evalBound, Slice.Inhabited_getElem_eq_getElem! _ _ outBound,
          eval_from_word _ _ _ _ _ _ outBound, ite_eq_right (by omega)]
      have body : horner_kernel_loop0.body loadModel storeModel cl leading rest
          (stateAt points out points.length) back = .ok (.done (back (stateAt points out points.length))) := by
        simp only [horner_kernel_loop0.body, zip_done _ _ _ (by omega), bind_ok]
        rfl
      conv_lhs => unfold horner_kernel_loop0 loop
      dsimp only
      rw [body, bind_ok, terminalOutput]

end BulksketchBridge.AvxHorner
