import Arithmetic.AvxMultiplyLinearGenerated
import BulksketchBridge.AvxSquareWindows

namespace BulksketchBridge.AvxMultiplyLinear

open Aeneas Aeneas.Std Aeneas.Std.Avx512Register Aeneas.Std.AvxSquareRuntime
open BulksketchBridge.Avx512RegisterChallenges AvxSquare
open bulksketch.backend.x86_vpclmul512
open SliceKernelChallenges X86MaskedMemory

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

def blockStart (stop : Nat) : Nat := max (stop - 8) 1

def rootRegister (root : U64) : Word512 := fun _ _ => root.bv

def blockRegister (words : Slice U64) (root : U64) (start stop : Nat) : Word512 :=
  xorRegister (loadWords (ClosedLeaf.region words start stop))
    (productsReduced (loadWords (ClosedLeaf.region words (start - 1) (stop - 1))) (rootRegister root))

def blockWrite (words : Slice U64) (root : U64) (start stop : Nat) : Slice U64 :=
  let region := ClosedLeaf.region words start stop
  if fits : region.length ≤ 8 then
    words.setSlice! start (storeWords region (blockRegister words root start stop) fits).val
  else words

theorem block_bounds (stop : Nat) (active : 1 < stop) :
    1 ≤ blockStart stop ∧ blockStart stop < stop ∧ stop - blockStart stop ≤ 8 := by
  unfold blockStart
  omega

@[simp] theorem block_write_length (words : Slice U64) (root : U64) (start stop : Nat) :
    (blockWrite words root start stop).length = words.length := by
  unfold blockWrite
  dsimp only
  split <;> simp only [Slice.setSlice!_length]

private theorem saturated_value (stop : Usize) :
    (core.num.Usize.saturating_sub stop 8#usize).val = stop.val - 8 := by
  have bound : stop.val < 2 ^ System.Platform.numBits := stop.bv.isLt
  change (BitVec.ofNat System.Platform.numBits (max 0 (stop.val - (8#usize).val))).toNat = _
  rw [BitVec.toNat_ofNat]
  have eight : (8#usize).val = 8 := by simp
  rw [eight, Nat.max_eq_right (Nat.zero_le _), Nat.mod_eq_of_lt (by omega)]

theorem body_active (loadModel : Load) (storeModel : Store)
    (loadLaw : LoadLaw loadModel) (storeLaw : StoreLaw storeModel)
    (words : Slice U64) (root : U64) (stop : Usize)
    (active : 1 < stop.val) (room : stop.val ≤ words.length) :
    ∃ start : Usize, start.val = blockStart stop.val ∧
      multiply_linear_loop.body loadModel storeModel (rootRegister root) words stop =
        .ok (.cont (blockWrite words root start.val stop.val, start)) := by
  let start := core.cmp.impls.OrdUsize.max (core.num.Usize.saturating_sub stop 8#usize) 1#usize
  have startValue : start.val = blockStart stop.val := by
    simp only [start, core.cmp.impls.OrdUsize.max_val, saturated_value, blockStart]
    rfl
  obtain ⟨first, order, width⟩ := block_bounds stop.val active
  rw [← startValue] at first order width
  obtain ⟨lo, leftSub, leftValue, _⟩ := RawMulTable.normal_of_spec _ _
    (Usize.sub_spec (x := start) (y := 1#usize) (by exact first))
  obtain ⟨hi, rightSub, rightValue, _⟩ := RawMulTable.normal_of_spec _ _
    (Usize.sub_spec (x := stop) (y := 1#usize) (by omega))
  change lo.val = start.val - 1 at leftValue
  change hi.val = stop.val - 1 at rightValue
  have front := ClosedLeaf.shared_region_normal words start stop (by omega) room
  have previous := ClosedLeaf.shared_region_normal words lo hi (by omega) (by omega)
  have cut := ClosedLeaf.mutable_region_normal words start stop (by omega) room
  let current := ClosedLeaf.region words start.val stop.val
  let lower := ClosedLeaf.region words lo.val hi.val
  have currentLen : current.length = stop.val - start.val := ClosedLeaf.region_length _ _ _ room
  have lowerLen : lower.length = stop.val - start.val := by
    change (ClosedLeaf.region words lo.val hi.val).length = _
    rw [ClosedLeaf.region_length _ _ _ (by omega), leftValue, rightValue]
    omega
  have currentFits : current.length ≤ 8 := by omega
  have lowerFits : lower.length ≤ 8 := by omega
  have store := storeLaw current (blockRegister words root start.val stop.val) currentFits
  have cond : 1#usize < stop := by exact active
  refine ⟨start, startValue, ?_⟩
  simp only [multiply_linear_loop.body, cond, ite_true, lift, bind_ok]
  change (do
    let first ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U64)
      words ⟨start, stop⟩
    let lhs ← loadModel first
    let lo ← start - 1#usize
    let hi ← stop - 1#usize
    let previous ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U64)
      words ⟨lo, hi⟩
    let rhs ← loadModel previous
    let multiplied ← multiply true rhs (rootRegister root)
    let value ← xorWords lhs multiplied
    let (out, restore) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice U64)
      words ⟨start, stop⟩
    let result ← storeModel out value
    Result.ok (ControlFlow.cont (restore result, start))) = _
  simp only [Bind.bind, Slice.index_SliceIndexRangeUsizeSliceInst, front, bind_ok,
    show ClosedLeaf.region words start.val stop.val = current from rfl,
    loadLaw current currentFits, leftSub, rightSub, previous,
    show ClosedLeaf.region words lo.val hi.val = lower from rfl, loadLaw lower lowerFits,
    xorWords, Slice.index_mut_SliceIndexRangeUsizeSliceInst, cut]
  have multiplication := Avx512Register.multiply_refines true (loadWords lower) (rootRegister root)
  rw [multiplication, bind_ok]
  have reg : (fun pair half => loadWords current pair half ^^^
      productsReduced (loadWords lower) (rootRegister root) pair half) =
      blockRegister words root start.val stop.val := by
    simp only [blockRegister, lower, leftValue, rightValue, current]
    rfl
  rw [reg]
  have fits : (ClosedLeaf.region words start.val stop.val).length ≤ 8 := currentFits
  simp only [store, bind_ok, blockWrite, dite_eq_left fits]
  rfl

def Descending (original current : Slice U64) (root : U64) (stop : Nat) : Prop :=
  current.length = original.length ∧
    ∀ i, i < original.length →
      current[i]! = if i < stop then original[i]! else coefficientAfter original root i

private theorem region_word (words : Slice U64) (start stop index : Nat)
    (room : stop ≤ words.length) (inside : start + index < stop) :
    (ClosedLeaf.region words start stop)[index]! = words[start + index]! := by
  simp only [ClosedLeaf.region, Slice.getElem!_Nat_eq, Slice.from_val]
  exact List.getElem!_slice start stop index words.val ⟨room, inside⟩

private theorem store_word (words : Slice U64) (value : Word512) (bound : words.length ≤ 8)
    (slot : Nat) (active : slot < words.length) :
    (storeWords words value bound)[slot]!.bv = flatten value ⟨slot, by omega⟩ := by
  have length : (storeWords words value bound).length = words.length := by
    simp [storeWords, registerPayload, Slice.length]
  rw [← Slice.Inhabited_getElem_eq_getElem! _ _ (by omega : slot < (storeWords words value bound).length)]
  rw [Slice.getElem_Nat_eq]
  simp only [storeWords, registerPayload, Slice.from_val, List.getElem_map, List.getElem_ofFn]
  change slot < (storeWords words value bound).length
  omega

theorem block_progress (original current : Slice U64) (root : U64) (stop : Nat)
    (active : 1 < stop) (room : stop ≤ original.length)
    (inv : Descending original current root stop) :
    Descending original (blockWrite current root (blockStart stop) stop) root (blockStart stop) := by
  let start := blockStart stop
  obtain ⟨positive, order, limited⟩ := block_bounds stop active
  change 1 ≤ start at positive
  change start < stop at order
  change stop - start ≤ 8 at limited
  let region := ClosedLeaf.region current start stop
  have roomNow : stop ≤ current.length := by rwa [inv.1]
  have regionLen : region.length = stop - start := ClosedLeaf.region_length _ _ _ roomNow
  have fits : region.length ≤ 8 := by omega
  let stored := storeWords region (blockRegister current root start stop) fits
  have storedLen : stored.length = stop - start := by
    have same : stored.length = region.length := by simp [stored, storeWords, registerPayload, Slice.length]
    exact same.trans regionLen
  refine ⟨(block_write_length ..).trans inv.1, ?_⟩
  intro index indexRoom
  have step : blockWrite current root start stop = current.setSlice! start stored.val := by
    simp only [blockWrite, show ClosedLeaf.region current start stop = region from rfl, dite_eq_left fits, stored]
  rw [step]
  by_cases before : index < start
  · rw [ite_eq_left before, Slice.setSlice!_getElem!_prefix _ _ _ _ before, inv.2 index indexRoom,
      ite_eq_left (by omega : index < stop)]
  · rw [ite_eq_right before]
    by_cases after : stop ≤ index
    · rw [Slice.setSlice!_getElem!_suffix _ _ _ _ (by change start + stored.length ≤ index; omega),
        inv.2 index indexRoom, ite_eq_right (by omega : ¬ index < stop)]
    · let lane : Fin 8 := ⟨index - start, by omega⟩
      have laneRegion : lane.val < region.length := by change index - start < _; omega
      have middle := Slice.setSlice!_getElem!_middle current stored.val start index (by
        change start ≤ index ∧ index - start < stored.length ∧ index < current.length
        omega)
      rw [middle, ← Slice.getElem!_Nat_eq]
      apply U64.bv_eq_imp_eq
      have written := store_word region (blockRegister current root start stop) fits lane.val laneRegion
      change (stored[lane.val]!).bv = _
      rw [written]
      have lowerLen : (ClosedLeaf.region current (start - 1) (stop - 1)).length = stop - start := by
        rw [ClosedLeaf.region_length _ _ _ (by omega)]
        omega
      have lowerRoom : lane.val < (ClosedLeaf.region current (start - 1) (stop - 1)).length := by
        rw [lowerLen, ← regionLen]
        exact laneRegion
      have thisWord := region_word current start stop lane.val roomNow (by change start + (index - start) < stop; omega)
      have priorWord := region_word current (start - 1) (stop - 1) lane.val (by omega)
        (by change start - 1 + (index - start) < stop - 1; omega)
      rw [show start + lane.val = index by dsimp [lane]; omega] at thisWord
      rw [show start - 1 + lane.val = index - 1 by dsimp [lane]; omega] at priorWord
      have selected : flatIndex ⟨lane.val / 2, by have := lane.isLt; omega⟩
          (decide (lane.val % 2 = 1)) = lane := by
        apply Fin.ext
        simp only [flatIndex, decide_eq_true_eq]
        split <;> omega
      simp only [blockRegister, xorRegister, productsReduced, loadWords, rootRegister, flatten,
        selected, show lane.val < (ClosedLeaf.region current start stop).length from laneRegion,
        lowerRoom, ite_true, thisWord, priorWord, coefficientAfter, ite_eq_right (by omega : index ≠ 0)]
      rw [inv.2 index indexRoom, inv.2 (index - 1) (by omega),
        ite_eq_left (by omega : index < stop), ite_eq_left (by omega : index - 1 < stop)]
      rfl

theorem initial_descending (words : Slice U64) (root : U64) :
    Descending words words root words.length := by
  refine ⟨rfl, ?_⟩
  intro i active
  rw [ite_eq_left active]

theorem finished_descending (original current : Slice U64) (root : U64) (stop : Nat)
    (inactive : stop ≤ 1) (inv : Descending original current root stop) :
    current = RebuiltLfsr.linearStep original root := by
  apply Slice.ext_getElem (inv.1.trans (RebuiltLfsr.linear_length _ _).symm)
  intro index leftRoom rightRoom
  have originalRoom : index < original.length := by rwa [← inv.1]
  rw [Slice.Inhabited_getElem_eq_getElem! _ _ leftRoom,
    Slice.Inhabited_getElem_eq_getElem! _ _ rightRoom, inv.2 index originalRoom]
  have rightWord : (RebuiltLfsr.linearStep original root)[index]! = coefficientAfter original root index := by
    simp only [RebuiltLfsr.linearStep, Slice.getElem!_Nat_eq, Slice.from_val]
    rw [← List.Inhabited_getElem_eq_getElem! _ index (by simpa using originalRoom), List.getElem_ofFn]
  rw [rightWord]
  split
  · rename_i early
    have first : index = 0 := by omega
    subst index
    simp only [coefficientAfter, ite_true]
  · rfl

theorem loop_refines (loadModel : Load) (storeModel : Store)
    (loadLaw : LoadLaw loadModel) (storeLaw : StoreLaw storeModel)
    (original current : Slice U64) (root : U64) (stop : Usize)
    (room : stop.val ≤ original.length) (inv : Descending original current root stop.val) :
    multiply_linear_loop loadModel storeModel current (rootRegister root) stop =
      .ok (RebuiltLfsr.linearStep original root) := by
  suffices ∀ endValue (stop : Usize) (current : Slice U64), stop.val = endValue →
      stop.val ≤ original.length → Descending original current root stop.val →
      multiply_linear_loop loadModel storeModel current (rootRegister root) stop =
        .ok (RebuiltLfsr.linearStep original root) from this stop.val stop current rfl room inv
  intro endValue
  induction endValue using Nat.strong_induction_on with
  | h endValue ih =>
    intro stop current exactStop room inv
    by_cases active : 1 < stop.val
    · obtain ⟨start, startValue, body⟩ :=
        body_active loadModel storeModel loadLaw storeLaw current root stop active (by rwa [inv.1])
      have lower := (block_bounds stop.val active).2.1
      have progress := block_progress original current root stop.val active room inv
      rw [← startValue] at progress
      conv_lhs => unfold multiply_linear_loop loop
      dsimp only
      rw [body, bind_ok]
      exact ih start.val (by omega) start (blockWrite current root start.val stop.val) rfl (by omega) progress
    · have stopTest : ¬ 1#usize < stop := by exact active
      have body : multiply_linear_loop.body loadModel storeModel (rootRegister root) current stop =
          .ok (.done current) := by simp only [multiply_linear_loop.body, stopTest, ite_false]
      conv_lhs => unfold multiply_linear_loop loop
      dsimp only
      rw [body, bind_ok]
      exact congrArg Result.ok (finished_descending original current root stop.val (by omega) inv)

private theorem signed_bits (word : U64) :
    (core.num.I64.from_le_bytes (core.num.U64.to_le_bytes word)).bv = word.bv := by
  have packed := X86Pclmul.word_refines word
  simp only [bulksketch.backend.x86_pclmul.word, X86PclmulRuntime.unsignedBytes,
    X86PclmulRuntime.signedFromBytes, X86PclmulRuntime.moveIn, bind_ok] at packed
  have equality := Result.ok_injective packed
  have narrowed := congrArg (fun bits : BitVec 128 => bits.setWidth 64) equality
  simpa only [BitVec.setWidth_setWidth_of_le _ (by decide : 64 ≤ 128), BitVec.setWidth_eq] using narrowed

/-- Exact original AVX in-place fixed-length linear product, including
empty/single-word slices and every short reverse block. -/
def ActualMultiplyLinear : Prop :=
  ∀ (loadModel : Load) (storeModel : Store), LoadLaw loadModel → StoreLaw storeModel →
    ∀ (words : Slice U64) (root : U64),
      multiply_linear loadModel storeModel words root = .ok (RebuiltLfsr.linearStep words root)

theorem multiply_linear_refines : ActualMultiplyLinear := by
  intro loadModel storeModel loadLaw storeLaw words root
  have original := initial_descending words root
  have stop : (Slice.len words).val = words.length := Slice.len_val _
  simp only [multiply_linear, X86PclmulRuntime.unsignedBytes, X86PclmulRuntime.signedFromBytes,
    broadcast, bind_ok, signed_bits]
  exact loop_refines loadModel storeModel loadLaw storeLaw words words root (Slice.len words)
    (by rw [stop]) (by rwa [stop])

end BulksketchBridge.AvxMultiplyLinear
