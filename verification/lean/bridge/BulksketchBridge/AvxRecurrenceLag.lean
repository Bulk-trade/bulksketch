import Arithmetic.AvxRecurrenceGenerated
import BulksketchBridge.AvxSquareBlocks
import BulksketchBridge.OddRecurrence

namespace BulksketchBridge.AvxRecurrence

open Aeneas Aeneas.Std Aeneas.Std.WP Aeneas.Std.Avx512Register Aeneas.Std.AvxSquareRuntime
open Algebra.Gf64 BulksketchProofs.Field AvxSquare Avx512RegisterChallenges X86MaskedMemory OddRecurrence
open bulksketch.backend.x86_vpclmul512
open scoped BigOperators

set_option maxRecDepth 4096
set_option maxHeartbeats 2500000

private abbrev Inclusive := core.ops.range.RangeInclusive Usize

private theorem read_normal (words : Slice U64) (index : Usize)
    (bounded : index.val < words.length) :
    Slice.index_usize words index = Result.ok words[index.val]! := by
  obtain ⟨value, normal, exactWord⟩ := RawMulTable.normal_of_spec _ _
    (Slice.index_usize_spec words index bounded)
  rw [normal, exactWord, Slice.getElem!_Nat_eq]
  exact congrArg Result.ok (List.Inhabited_getElem_eq_getElem! words.val index.val bounded)

private def lagCount (range : Inclusive) : Nat :=
  if range.exhausted then 0 else range.«end».val + 1 - range.start.val

private theorem inclusive_step (range : Inclusive)
    (active : ¬ (range.exhausted = true ∨ range.«end».val < range.start.val)) :
    ∃ next : Inclusive,
      core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
        core.iter.range.StepUsize range = Result.ok (some range.start, next) ∧
      next.«end» = range.«end» ∧ range.start.val ≤ next.start.val ∧
      lagCount range = lagCount next + 1 ∧
      (lagCount next = 0 ∨ next.start.val = range.start.val + 1) := by
  obtain ⟨⟨option, next⟩, normal, post⟩ := RawMulTable.normal_of_spec _ _
    (core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next_Usize_spec range)
  have unexhausted : range.exhausted = false := by
    cases hex : range.exhausted <;> simp_all
  simp only [uncurry'_pair, ite_eq_right active] at post
  by_cases advanced : range.start.val < range.«end».val
  · rw [ite_eq_left advanced] at post
    obtain ⟨rfl, startEq, endEq, exhaustedEq⟩ := post
    refine ⟨next, normal, endEq, by omega, ?_, Or.inr startEq⟩
    simp only [lagCount, unexhausted, exhaustedEq, Bool.false_eq_true, ite_false, endEq, startEq]
    omega
  · rw [ite_eq_right advanced] at post
    obtain ⟨rfl, startEq, endEq, exhaustedEq⟩ := post
    refine ⟨next, normal, endEq, by simp only [startEq]; omega, ?_, ?_⟩
    · simp only [lagCount, unexhausted, exhaustedEq, Bool.false_eq_true, ite_false, ite_true]
      omega
    · left
      simp [lagCount, exhaustedEq]

private theorem inclusive_done (range : Inclusive)
    (stopped : range.exhausted = true ∨ range.«end».val < range.start.val) :
    core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
      core.iter.range.StepUsize range = Result.ok (none, range) ∧ lagCount range = 0 := by
  obtain ⟨⟨option, next⟩, normal, post⟩ := RawMulTable.normal_of_spec _ _
    (core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next_Usize_spec range)
  simp only [uncurry'_pair, ite_eq_left stopped] at post
  obtain ⟨rfl, rfl⟩ := post
  refine ⟨normal, ?_⟩
  rcases stopped with exhausted | beyond
  · simp [lagCount, exhausted]
  · simp only [lagCount]
    split <;> omega

private theorem sum_step (odd locator : Slice U64) (index : Nat) (range next : Inclusive)
    (count : lagCount range = lagCount next + 1)
    (nextStart : lagCount next = 0 ∨ next.start.val = range.start.val + 1) :
    lagSum odd locator index range.start.val (lagCount range) =
      lagTerm odd locator index range.start.val + lagSum odd locator index next.start.val (lagCount next) := by
  simp only [lagSum, count, Finset.sum_range_succ', Nat.add_zero]
  rw [add_comm]
  apply congrArg (fun value : Field => lagTerm odd locator index range.start.val + value)
  rcases nextStart with exhausted | advance
  · simp [exhausted]
  · rw [advance]
    apply Finset.sum_congr rfl
    intro offset _
    exact congrArg (lagTerm odd locator index) (by omega)

noncomputable def reducedLane (even upper : Word512) (pair : Fin 4) (half : Bool) : Field :=
  toField (reduceRegisters even upper pair half)

private theorem signedBits (word : U64) :
    (core.num.I64.from_le_bytes (core.num.U64.to_le_bytes word)).bv = word.bv := by
  have packed := X86Pclmul.word_refines word
  simp only [bulksketch.backend.x86_pclmul.word, X86PclmulRuntime.unsignedBytes,
    X86PclmulRuntime.signedFromBytes, X86PclmulRuntime.moveIn, bind_ok] at packed
  have equality := Result.ok_injective packed
  have narrowed := congrArg (fun bits : BitVec 128 => bits.setWidth 64) equality
  simpa only [BitVec.setWidth_setWidth_of_le _ (by decide : 64 ≤ 128), BitVec.setWidth_eq] using narrowed

private theorem reduction_add (input scale even upper : Word512) (pair : Fin 4) (half : Bool) :
    reducedLane (xorRegister even (products input scale false))
      (xorRegister upper (products input scale true)) pair half =
      reducedLane even upper pair half + toField (input pair half) * toField (scale pair half) := by
  cases half <;> simp only [reducedLane, reduceRegisters, Bool.false_eq_true, ite_false, ite_true,
    xorRegister, products, reduceFold64_xor, toField_xor] <;>
    apply congrArg (_ + ·) <;> exact toField_mul _ _

private theorem load_lane (words : Slice U64) (start stop : Nat) (pair : Fin 4) (half : Bool)
    (endRoom : stop ≤ words.length) (inBlock : (flatIndex pair half).val < stop - start) :
    loadWords (ClosedLeaf.region words start stop) pair half =
      words[start + (flatIndex pair half).val]!.bv := by
  rw [loadWords, ClosedLeaf.region_length _ _ _ endRoom, ite_eq_left inBlock]
  simp only [ClosedLeaf.region, Slice.getElem!_Nat_eq, Slice.from_val]
  rw [List.getElem!_slice _ _ _ _ ⟨endRoom, by omega⟩]

private theorem lag_step (loadModel : Load) (law : LoadLaw loadModel)
    (odd locator : Slice U64) (index len : Usize) (range : Inclusive)
    (even upper : Word512) (active : ¬ (range.exhausted = true ∨ range.«end».val < range.start.val))
    (lagBound : range.«end».val ≤ index.val) (locatorRoom : range.«end».val < locator.length)
    (endRoom : index.val + len.val ≤ odd.length) (short : len.val ≤ 8) :
    ∃ next resultEven resultUpper,
      odd_recurrence_matches_loop0_loop0.body loadModel odd locator index len range even upper =
        .ok (.cont (next, resultEven, resultUpper)) ∧
      next.«end» = range.«end» ∧ range.start.val ≤ next.start.val ∧
      lagCount range = lagCount next + 1 ∧ (lagCount next = 0 ∨ next.start.val = range.start.val + 1) ∧
      ∀ pair half, (flatIndex pair half).val < len.val →
        reducedLane resultEven resultUpper pair half = reducedLane even upper pair half +
          lagTerm odd locator (index.val + (flatIndex pair half).val) range.start.val := by
  have live : range.start.val ≤ range.«end».val := by omega
  obtain ⟨next, nextNormal, endEq, startMono, consumed, nextStart⟩ := inclusive_step range active
  obtain ⟨start, startNormal, startPost⟩ := RawMulTable.normal_of_spec _ _
    (Usize.sub_spec (x := index) (y := range.start) (by omega))
  have startVal : start.val = index.val - range.start.val := startPost.1
  obtain ⟨stop, stopNormal, stopVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := start) (y := len) (by
      have oddMax : odd.length ≤ Usize.max := odd.length_ineq
      change start.val + len.val ≤ Usize.max
      omega))
  change stop.val = start.val + len.val at stopVal
  have fits : stop.val ≤ odd.length := by omega
  have window := ClosedLeaf.shared_region_normal odd start stop (by omega) fits
  let row := loadWords (ClosedLeaf.region odd start.val stop.val)
  let scale : Word512 := fun _ _ => locator[range.start.val]!.bv
  have blockWidth : (ClosedLeaf.region odd start.val stop.val).length = len.val := by
    rw [ClosedLeaf.region_length _ _ _ fits, stopVal, Nat.add_sub_cancel_left]
  have loaded : loadModel (ClosedLeaf.region odd start.val stop.val) = .ok row := law _ (by rwa [blockWidth])
  have coefficient := read_normal locator range.start (by omega)
  have exactRaw : raw row scale = Result.ok (products row scale false, products row scale true) :=
    BulksketchBridge.Avx512Register.raw_refines row scale
  refine ⟨next, xorRegister even (products row scale false), xorRegister upper (products row scale true),
    ?_, endEq, startMono, consumed, nextStart, ?_⟩
  · simp only [odd_recurrence_matches_loop0_loop0.body, nextNormal, bind_ok]
    dsimp! only
    simp only [startNormal, stopNormal, core.slice.index.Slice.index, window, loaded,
      coefficient, X86PclmulRuntime.unsignedBytes, X86PclmulRuntime.signedFromBytes, broadcast, signedBits,
      bind_ok]
    rw [exactRaw]
    simp only [bind_ok]
    dsimp! only
    simp only [xorWords, bind_ok]
    rfl
  · intro pair half inBlock
    rw [reduction_add]
    unfold row
    rw [load_lane odd start.val stop.val pair half fits (by omega)]
    have exactIndex : start.val + (flatIndex pair half).val =
        index.val + (flatIndex pair half).val - range.start.val := by omega
    rw [exactIndex]
    rfl

theorem inner_lag_loop (loadModel : Load) (law : LoadLaw loadModel)
    (odd locator : Slice U64) (index len : Usize)
    (endRoom : index.val + len.val ≤ odd.length) (short : len.val ≤ 8)
    (range : Inclusive) (even upper : Word512)
    (lagBound : range.«end».val ≤ index.val) (locatorRoom : range.«end».val < locator.length) :
    ∃ resultEven resultUpper,
      odd_recurrence_matches_loop0_loop0 loadModel range odd locator index len even upper =
        .ok (resultEven, resultUpper) ∧
      ∀ pair half, (flatIndex pair half).val < len.val →
        reducedLane resultEven resultUpper pair half = reducedLane even upper pair half +
          lagSum odd locator (index.val + (flatIndex pair half).val) range.start.val (lagCount range) := by
  suffices ∀ count (range : Inclusive) (even upper : Word512),
      lagCount range = count → range.«end».val ≤ index.val → range.«end».val < locator.length →
      ∃ resultEven resultUpper,
        odd_recurrence_matches_loop0_loop0 loadModel range odd locator index len even upper =
          .ok (resultEven, resultUpper) ∧
        ∀ pair half, (flatIndex pair half).val < len.val →
          reducedLane resultEven resultUpper pair half = reducedLane even upper pair half +
            lagSum odd locator (index.val + (flatIndex pair half).val) range.start.val (lagCount range) from
    this (lagCount range) range even upper rfl lagBound locatorRoom
  intro count
  induction count using Nat.strong_induction_on with
  | h count ih =>
    intro range even upper countEq lagBound locatorRoom
    by_cases stop : range.exhausted = true ∨ range.«end».val < range.start.val
    · obtain ⟨next, zero⟩ := inclusive_done range stop
      refine ⟨even, upper, ?_, ?_⟩
      · unfold odd_recurrence_matches_loop0_loop0 loop
        dsimp only
        simp only [odd_recurrence_matches_loop0_loop0.body, next, bind_ok]
        dsimp! only
        simp only [bind_ok]
      · intro pair half _
        simp [lagSum, zero]
    · obtain ⟨next, newEven, newUpper, normal, endEq, _, consumed, nextStart, step⟩ :=
        lag_step loadModel law odd locator index len range even upper stop lagBound locatorRoom endRoom short
      obtain ⟨resultEven, resultUpper, ran, meaning⟩ := ih (lagCount next) (by omega)
        next newEven newUpper rfl (by rwa [endEq]) (by rwa [endEq])
      refine ⟨resultEven, resultUpper, ?_, ?_⟩
      · unfold odd_recurrence_matches_loop0_loop0 loop
        dsimp only
        rw [normal]
        simpa only [odd_recurrence_matches_loop0_loop0, bind_ok] using ran
      · intro pair half inBlock
        rw [meaning pair half inBlock, step pair half inBlock,
          sum_step odd locator _ range next consumed nextStart, add_assoc]

theorem lag_block_sum (loadModel : Load) (law : LoadLaw loadModel)
    (odd locator : Slice U64) (index len degree : Usize)
    (lagBound : degree.val ≤ index.val) (locatorRoom : degree.val < locator.length)
    (endRoom : index.val + len.val ≤ odd.length) (short : len.val ≤ 8) :
    ∃ even upper,
      odd_recurrence_matches_loop0_loop0 loadModel ⟨1#usize, degree, false⟩ odd locator index len
        (fun _ _ => 0) (fun _ _ => 0) = .ok (even, upper) ∧
      ∀ pair half, (flatIndex pair half).val < len.val →
        reducedLane even upper pair half =
          lagSum odd locator (index.val + (flatIndex pair half).val) 1 degree.val := by
  obtain ⟨even, upper, ran, meaning⟩ := inner_lag_loop loadModel law odd locator index len endRoom short
    ⟨1#usize, degree, false⟩ (fun _ _ => 0) (fun _ _ => 0) lagBound locatorRoom
  refine ⟨even, upper, ran, ?_⟩
  intro pair half inBlock
  have zero : reducedLane (fun _ _ => 0) (fun _ _ => 0) pair half = 0 := by
    cases half <;> simp [reducedLane, reduceRegisters, reduceFold64, fold64, overflow64] <;> exact toField_zero
  rw [meaning pair half inBlock, zero, zero_add]
  simp only [lagCount, Bool.false_eq_true, ite_false, show (1#usize).val = 1 from rfl, Nat.add_sub_cancel]

#print axioms lag_block_sum

end BulksketchBridge.AvxRecurrence
