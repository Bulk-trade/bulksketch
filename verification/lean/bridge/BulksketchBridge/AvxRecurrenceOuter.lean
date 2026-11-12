import BulksketchBridge.AvxRecurrenceBlockMask
import BulksketchBridge.AvxSquareBlocks
import BulksketchBridge.AffineEnumerationBatch
import BulksketchBridge.OddRecurrence

namespace BulksketchBridge.AvxRecurrence

open Aeneas Aeneas.Std Result Aeneas.Std.Avx512Register Aeneas.Std.AvxSquareRuntime
open Aeneas.Std.AvxRecurrenceRuntime
open BulksketchBridge.X86MaskedMemory BulksketchBridge.Algebra.Gf64
open BulksketchProofs.Field
open bulksketch.backend.x86_vpclmul512

set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

abbrev BlockIter := core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize)

def blockAt (index stop : Usize) : BlockIter :=
  AffineEnumerate.batchAt index stop 8#usize

abbrev reducedBlock := AvxSquare.reduceRegisters

/-- The exact lag loop returns the complete two packed raw registers. Their
pairwise reductions represent the scalar recurrence at each active lane. -/
def InnerBlockLaw (loadModel : Load) : Prop :=
  ∀ (odd squared : Slice U64) (index len degree : Usize),
    degree.val ≤ index.val → index.val + len.val ≤ odd.length →
    len.val ≤ 8 → degree.val < squared.length →
    ∃ even upper : Word512,
      odd_recurrence_matches_loop0_loop0 loadModel ⟨1#usize, degree, false⟩
        odd squared index len (fun _ _ => 0) (fun _ _ => 0) = .ok (even, upper) ∧
      ∀ pair half, (flatIndex pair half).val < len.val →
        toField (reducedBlock even upper pair half) =
          OddRecurrence.lagSum odd squared (index.val + (flatIndex pair half).val) 1 degree.val

def MatchesInterval (odd squared : Slice U64) (degree start stop : Nat) : Prop :=
  ∀ index : Nat, start ≤ index → index < stop →
    toField odd[index]!.bv = OddRecurrence.lagSum odd squared index 1 degree

private theorem region_word (odd : Slice U64) (start stop lane : Nat)
    (bounded : stop ≤ odd.length) (active : lane < stop - start) :
    (ClosedLeaf.region odd start stop)[lane]! = odd[start + lane]! := by
  simp only [ClosedLeaf.region, Slice.getElem!_Nat_eq, Slice.from_val, List.getElem!_eq_getElem?_getD]
  rw [List.getElem?_slice _ _ _ _ ⟨bounded, by omega⟩]

private theorem active_load_word (odd : Slice U64) (start stop : Nat) (pair : Fin 4) (half : Bool)
    (bounded : stop ≤ odd.length) (active : (flatIndex pair half).val < stop - start) :
    AvxSquare.loadWords (ClosedLeaf.region odd start stop) pair half =
      odd[start + (flatIndex pair half).val]!.bv := by
  unfold AvxSquare.loadWords
  rw [ClosedLeaf.region_length odd start stop bounded, ite_eq_left active,
    region_word odd start stop _ bounded active]

private theorem equality_matches_interval (odd squared : Slice U64) (degree start stop : Nat)
    (expected : Word512) (ordered : start ≤ stop) (bounded : stop ≤ odd.length)
    (width : stop - start ≤ 8)
    (reduced : ∀ pair half, (flatIndex pair half).val < stop - start →
      toField (expected pair half) =
        OddRecurrence.lagSum odd squared (start + (flatIndex pair half).val) 1 degree) :
    (∀ pair half, (flatIndex pair half).val < stop - start →
      expected pair half = AvxSquare.loadWords (ClosedLeaf.region odd start stop) pair half) ↔
      MatchesInterval odd squared degree start stop := by
  constructor
  · intro equal index atLeast before
    let lane : Fin 8 := ⟨index - start, by omega⟩
    obtain ⟨pair, half, laneEq⟩ := flat_index_surjective lane
    have exactLane : (flatIndex pair half).val = index - start := congrArg Fin.val laneEq
    have active : (flatIndex pair half).val < stop - start := by omega
    have indexEq : start + (flatIndex pair half).val = index := by omega
    have words := equal pair half active
    rw [active_load_word odd start stop pair half bounded active, indexEq] at words
    have recurrence := reduced pair half active
    rwa [indexEq, words] at recurrence
  · intro agrees pair half active
    rw [active_load_word odd start stop pair half bounded active]
    apply toField_injective
    exact (reduced pair half active).trans (agrees _ (by omega) (by omega)).symm

/-- The original outer body compares the correct reduced lag sum for every
active lane. A short tail masks all inactive lanes before the early exit. -/
theorem outer_block_active (loadModel : Load) (loadLaw : AvxSquare.LoadLaw loadModel)
    (innerLaw : InnerBlockLaw loadModel) (odd squared : Slice U64) (index degree : Usize)
    (degreeBound : degree.val < squared.length) (atLeast : degree.val ≤ index.val)
    (active : index.val < odd.length) :
    ∃ next : Usize, next.val = min (index.val + 8) odd.length ∧
      (MatchesInterval odd squared degree.val index.val next.val →
        odd_recurrence_matches_loop0.body loadModel odd squared degree (blockAt index odd.len) =
          .ok (.cont (blockAt next odd.len))) ∧
      (¬ MatchesInterval odd squared degree.val index.val next.val →
        odd_recurrence_matches_loop0.body loadModel odd squared degree (blockAt index odd.len) =
          .ok (.done false)) := by
  obtain ⟨next, iterNormal, nextValue⟩ := AffineEnumerate.next_batch index odd.len 8#usize
    (by simp) (by simpa only [Slice.len_val] using active)
  change (core.iter.adapters.step_by.IteratorStepBy.next
    (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) (blockAt index odd.len)) =
      .ok (some index, blockAt next odd.len) at iterNormal
  change next.val = min (index.val + 8) odd.len.val at nextValue
  rw [Slice.len_val] at nextValue
  obtain ⟨remaining, subtracted, remVal, _⟩ := RawMulTable.normal_of_spec _ _
    (Usize.sub_spec (x := odd.len) (y := index) (by rw [Slice.len_val]; omega))
  change remaining.val = odd.len.val - index.val at remVal
  rw [Slice.len_val] at remVal
  let len := core.cmp.impls.OrdUsize.min remaining 8#usize
  have lenVal : len.val = next.val - index.val := by
    simp only [len, core.cmp.impls.OrdUsize.min_val, remVal, show (8#usize).val = 8 from rfl]
    omega
  have ordered : index.val ≤ next.val := by omega
  have bounded : next.val ≤ odd.length := by omega
  have width : len.val ≤ 8 := by omega
  have stopValue : index.val + len.val = next.val := by omega
  obtain ⟨endWord, added, endValue⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := index) (y := len) (by rw [stopValue]; exact bounded.trans odd.length_ineq))
  have same : endWord = next := UScalar.eq_of_val_eq (endValue.trans stopValue)
  rw [same] at added
  let window := ClosedLeaf.region odd index.val next.val
  have windowLength : window.length = len.val :=
    (ClosedLeaf.region_length odd index.val next.val bounded).trans lenVal.symm
  have sliceNormal := ClosedLeaf.shared_region_normal odd index next ordered bounded
  have rangeNormal : core.ops.range.RangeInclusive.new 1#usize degree =
      .ok (⟨1#usize, degree, false⟩ : core.ops.range.RangeInclusive Usize) := rfl
  obtain ⟨even, upper, inner, reduced⟩ :=
    innerLaw odd squared index len degree atLeast (by rwa [stopValue]) width degreeBound
  obtain ⟨mask, maskNormal, _, bits⟩ := X86LaneMask.mask_refines len width
  have loaded : loadModel window = .ok (AvxSquare.loadWords window) := loadLaw window (by omega)
  have zeroMeaning :
      testWord (laneXor (reducedBlock even upper) (AvxSquare.loadWords window)) allOnes &&& mask = 0#u8 ↔
        MatchesInterval odd squared degree.val index.val next.val := by
    rw [masked_mismatch_zero_iff _ _ _ _ bits, lenVal]
    exact equality_matches_interval odd squared degree.val index.val next.val (reducedBlock even upper)
      ordered bounded (by omega) (by rwa [lenVal] at reduced)
  have unpacked :
      unpack false (Avx512RegisterChallenges.carrylessReduction even)
        (Avx512RegisterChallenges.carrylessReduction upper) = .ok (reducedBlock even upper) := by
    unfold unpack
    congr 1
    funext pair half
    cases half <;> rfl
  have xorNormal : xorWords (reducedBlock even upper) (AvxSquare.loadWords window) =
      .ok (laneXor (reducedBlock even upper) (AvxSquare.loadWords window)) := rfl
  have onesNormal : broadcast (-1)#i64 = .ok allOnes := rfl
  have body :
      odd_recurrence_matches_loop0.body loadModel odd squared degree (blockAt index odd.len) =
      if (testWord (laneXor (reducedBlock even upper) (AvxSquare.loadWords window)) allOnes &&& mask != 0#u8)
      then .ok (.done false) else .ok (.cont (blockAt next odd.len)) := by
    simp only [odd_recurrence_matches_loop0.body, iterNormal, bind_ok]
    dsimp! only
    simp only [subtracted, bind_ok, lift, AvxSquareRuntime.zero, rangeNormal]
    rw [inner]
    simp only [bind_ok]
    dsimp! only
    rw [Avx512Register.reduce_cl_refines even, bind_ok, Avx512Register.reduce_cl_refines upper, bind_ok,
      unpacked, bind_ok, added, bind_ok]
    simp only [Slice.index_SliceIndexRangeUsizeSliceInst]
    rw [sliceNormal, bind_ok, loaded, bind_ok, xorNormal, bind_ok, onesNormal, bind_ok,
      test_mask_normal, bind_ok, maskNormal, bind_ok]
  refine ⟨next, nextValue, ?_, ?_⟩
  · intro agrees
    rw [body, zeroMeaning.mpr agrees]
    simp
  · intro mismatch
    have nonzero : testWord (laneXor (reducedBlock even upper) (AvxSquare.loadWords window)) allOnes &&& mask ≠ 0#u8 :=
      fun zero => mismatch (zeroMeaning.mp zero)
    rw [body]
    simp [nonzero]

theorem outer_block_done (loadModel : Load) (odd squared : Slice U64) (index degree : Usize)
    (done : odd.length ≤ index.val) :
    odd_recurrence_matches_loop0.body loadModel odd squared degree (blockAt index odd.len) =
      .ok (.done true) := by
  have iter := AffineEnumerate.batches_done index odd.len 8#usize (by simp)
    (by simpa only [Slice.len_val] using done)
  change (core.iter.adapters.step_by.IteratorStepBy.next
    (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) (blockAt index odd.len)) =
      .ok (none, blockAt index odd.len) at iter
  simp only [odd_recurrence_matches_loop0.body, iter, bind_ok]
  rfl

#print axioms outer_block_active
#print axioms outer_block_done

end BulksketchBridge.AvxRecurrence
