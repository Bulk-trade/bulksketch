import BulksketchBridge.CandidateSupport
import Mathlib.Algebra.Polynomial.Roots

namespace BulksketchBridge.CandidateOuter

open Aeneas.Std Algebra.Gf64 SliceKernels DenseCoefficient BmEntry RebuiltLfsr
open bulksketch.decode.stages bulksketch.decode.row bulksketch.decode.scratch bulksketch.types
open Aeneas.Std.AvxHornerChunkRuntime (ChunkState window)

def matchingCandidates (coefficients : Slice U64) (words : List U64) : List U64 :=
  words.filter fun word => decide (PortableHornerChallenges.evalWord coefficients.val word = 0#u64)

private theorem zeros_count (coefficients : Slice U64) (words : List U64)
    (distinct : words.Nodup) (nonzero : slicePolynomial coefficients ≠ 0) :
    (matchingCandidates coefficients words).length ≤ (slicePolynomial coefficients).natDegree := by
  classical
  let selected := matchingCandidates coefficients words
  let fieldWords := selected.map (fun word => toField word.bv)
  let polynomial := slicePolynomial coefficients
  have selectedDistinct : selected.Nodup := List.filter_sublist.nodup distinct
  have fieldDistinct : fieldWords.Nodup :=
    selectedDistinct.map (fun a b h => U64.bv_eq_imp_eq a b (toField_injective h))
  have subset : fieldWords.toFinset ⊆ polynomial.roots.toFinset := by
    intro root present
    obtain ⟨word, member, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp present)
    have evaluates : PortableHornerChallenges.evalWord coefficients.val word = 0#u64 :=
      of_decide_eq_true (List.mem_filter.mp member).2
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots nonzero).mpr
    change (slicePolynomial coefficients).eval (toField word.bv) = 0
    rw [← PortableHorner.horner_word_evaluates, evaluates]
    exact toField_zero
  calc
    selected.length = fieldWords.length := by simp [fieldWords]
    _ = fieldWords.toFinset.card := (List.toFinset_card_of_nodup fieldDistinct).symm
    _ ≤ polynomial.roots.toFinset.card := Finset.card_le_card subset
    _ ≤ polynomial.roots.card := Multiset.toFinset_card_le _
    _ ≤ polynomial.natDegree := Polynomial.card_roots' _

private theorem zero_pairs (coefficients : Slice U64) (words suffix : List U64) :
    CandidateInner.zeroPoints (List.zip words
        (words.map (PortableHornerChallenges.evalWord coefficients.val) ++ suffix)) =
      matchingCandidates coefficients words := by
  induction words with
  | nil => rfl
  | cons head tail ih =>
    by_cases zero : PortableHornerChallenges.evalWord coefficients.val head = 0#u64
    · simp only [matchingCandidates, List.map_cons, List.cons_append, List.zip_cons_cons,
        CandidateInner.zeroPoints, zero, ite_true, decide_true, List.filter_cons_of_pos]
      rw [ih]
      rfl
    · simp only [matchingCandidates, List.map_cons, List.cons_append, List.zip_cons_cons,
        CandidateInner.zeroPoints, zero, ite_false, decide_false, List.filter_cons, Bool.false_eq_true]
      exact ih

private theorem chunk_complete (coefficients points roots values : Slice U64) (degree hits : Nat)
    (rootRoom : degree ≤ roots.length) (room : points.length ≤ values.length)
    (admitted : hits + (matchingCandidates coefficients points.val).length ≤ degree) :
    let result := chunkResult coefficients points roots values degree hits
    result.1 = hits + (matchingCandidates coefficients points.val).length ∧
    result.2.1.length = roots.length ∧ result.2.2.1.length = values.length ∧ result.2.2.2 = false := by
  dsimp only
  let scratch := restorePrefix values (evaluated coefficients points)
  have prefixVals : scratch.val = points.val.map (PortableHornerChallenges.evalWord coefficients.val)
      ++ values.val.drop points.length := by
    change points.val.length ≤ values.val.length at room
    simp only [scratch, restorePrefix, evaluated, Slice.from_val, List.setSlice!, List.take_zero,
      Nat.sub_zero, Nat.zero_add, List.nil_append, List.length_map, Nat.min_eq_left room]
    rw [List.take_of_length_le (by simp)]
  have paired : CandidateInner.zeroPoints (List.zip points.val scratch.val) = matchingCandidates coefficients points.val := by
    rw [prefixVals, zero_pairs]
  have frame := CandidateInner.scan_frame degree (List.zip points.val scratch.val) roots hits rootRoom (by omega)
  simp only [CandidateInner.ScanFrame, paired] at frame
  obtain ⟨count, _, writtenLen, _, rejected⟩ := frame
  have fits : (matchingCandidates coefficients points.val).length ≤ degree - hits := by omega
  rw [List.take_of_length_le fits] at count
  rw [decide_eq_false (Nat.not_lt.mpr fits)] at rejected
  exact ⟨count, writtenLen, restore_length _ _, rejected⟩

/-- An admitted total root count prevents every early rejection and all
eligible candidates are counted after exhausting the original chunk cursor. -/
theorem chunks_complete (coefficients : Slice U64) (degree fuel : Nat) (cursor : ChunkState U64)
    (hits : Nat) (roots values : Slice U64)
    (rootRoom : degree ≤ roots.length) (positive : 0 < cursor.width)
    (width : cursor.width ≤ values.length) (enough : cursor.words.length - cursor.offset ≤ fuel)
    (admitted : hits + (matchingCandidates coefficients (cursor.words.val.drop cursor.offset)).length ≤ degree) :
    let result := runChunks coefficients degree fuel cursor hits roots values
    result.1 = hits + (matchingCandidates coefficients (cursor.words.val.drop cursor.offset)).length ∧
      result.2.2.2 = false := by
  induction fuel generalizing cursor hits roots values with
  | zero =>
    have empty : cursor.words.val.drop cursor.offset = [] := by
      apply List.drop_eq_nil_of_le
      change cursor.words.length ≤ cursor.offset
      omega
    simp [runChunks, empty, matchingCandidates]
  | succ fuel ih =>
    by_cases active : cursor.offset < cursor.words.length
    · let stop := min (cursor.offset + cursor.width) cursor.words.length
      let points := window cursor.words cursor.offset stop
      let next : ChunkState U64 := { cursor with offset := stop }
      have advance : cursor.offset < stop := by
        unfold stop
        exact Nat.lt_min.mpr ⟨by omega, active⟩
      have stopBound : stop ≤ cursor.words.length := Nat.min_le_right _ _
      have pointLength : points.length = stop - cursor.offset := by
        simp only [points, window, Slice.length, Slice.from_val, List.slice_length]
        exact Nat.min_eq_right (Nat.sub_le_sub_right stopBound _)
      have room : points.length ≤ values.length := by
        have stopWidth : stop ≤ cursor.offset + cursor.width := Nat.min_le_left _ _
        omega
      have remaining : (cursor.words.val.drop cursor.offset).drop (stop - cursor.offset) =
          cursor.words.val.drop stop := by
        rw [List.drop_drop, Nat.add_sub_of_le advance.le]
      have partition : points.val ++ cursor.words.val.drop stop = cursor.words.val.drop cursor.offset := by
        simp only [points, window, Slice.from_val, List.slice]
        rw [← remaining, List.take_append_drop]
      have splitZeros : (matchingCandidates coefficients points.val).length +
          (matchingCandidates coefficients (cursor.words.val.drop stop)).length =
          (matchingCandidates coefficients (cursor.words.val.drop cursor.offset)).length := by
        rw [← partition]
        simp only [matchingCandidates, List.filter_append, List.length_append]
      have stepFrame := chunk_complete coefficients points roots values degree hits rootRoom room (by omega)
      obtain ⟨count, written, scratch, reject, step⟩ :
          ∃ count written scratch reject,
            chunkResult coefficients points roots values degree hits = (count, written, scratch, reject) :=
        ⟨_, _, _, _, Prod.eta _ |>.symm.trans (by rfl)⟩
      rw [step] at stepFrame
      obtain ⟨counted, rootsLen, valuesLen, stopped⟩ := stepFrame
      change count = hits + (matchingCandidates coefficients points.val).length at counted
      change written.length = roots.length at rootsLen
      change scratch.length = values.length at valuesLen
      change reject = false at stopped
      subst reject
      have result := ih next count written scratch (by rwa [rootsLen]) positive
        (by change cursor.width ≤ scratch.length; rwa [valuesLen])
        (by change cursor.words.length - stop ≤ fuel; omega)
        (by change count + (matchingCandidates coefficients (cursor.words.val.drop stop)).length ≤ degree; omega)
      simp only [runChunks, active, ite_true]
      change (let (n, r, v, reject) := chunkResult coefficients points roots values degree hits
        if reject then (n, r, v, reject) else runChunks coefficients degree fuel next n r v).1 =
          hits + (matchingCandidates coefficients (cursor.words.val.drop cursor.offset)).length ∧ _
      rw [step]
      simp only [Bool.false_eq_true, ite_false]
      obtain ⟨total, notRejected⟩ := result
      refine ⟨?_, notRejected⟩
      change (runChunks coefficients degree fuel next count written scratch).1 = _ at total ⊢
      rw [total, counted]
      change hits + (matchingCandidates coefficients points.val).length +
        (matchingCandidates coefficients (cursor.words.val.drop stop)).length = _
      omega
    · have empty : cursor.words.val.drop cursor.offset = [] := by
        apply List.drop_eq_nil_of_le
        change cursor.words.length ≤ cursor.offset
        omega
      simp [runChunks, active, empty, matchingCandidates]

private theorem entry_complete {K : Type} (self : Execution bulksketch.field.Gf64 K)
    (input : RowInput) (workspace : RowWorkspace) (bounds : CandidateEntryBounds self input workspace)
    (fresh : self.hits.val = 0) (distinct : input.candidates.val.Nodup)
    (monic : (slicePolynomial (prefixSlice workspace.bm (self.degree.val + 1))).Monic)
    (degreeBound : (slicePolynomial (prefixSlice workspace.bm (self.degree.val + 1))).natDegree ≤ self.degree.val) :
    let result := candidateEntryModel self input workspace
    result.1 = (matchingCandidates (prefixSlice workspace.bm (self.degree.val + 1)) input.candidates.val).length ∧
      result.2.2.2 = false := by
  obtain ⟨degreeRoom, buffers, rootRoom, _⟩ := bounds
  let width := input.difference.length + 1
  let locator := prefixSlice workspace.bm width
  let coefficients := prefixSlice workspace.bm (self.degree.val + 1)
  let values := prefixSlice (tail workspace.bm width) width
  let cursor : ChunkState U64 := ⟨input.candidates, 0, width⟩
  have widthVal : values.length = width := by
    unfold values
    rw [prefix_length, tail_length, Nat.min_eq_left (by omega)]
  have locatorEq : prefixSlice locator (self.degree.val + 1) = coefficients := by
    apply Slice.ext
    simp only [locator, coefficients, prefixSlice, Slice.from_val, List.take_take]
    rw [Nat.min_eq_left (by omega : self.degree.val + 1 ≤ width)]
  have rootCount := (zeros_count coefficients input.candidates.val distinct monic.ne_zero).trans degreeBound
  have normal := chunks_complete coefficients self.degree.val input.candidates.length cursor self.hits.val
    workspace.roots values rootRoom (by change 0 < width; omega)
    (by change width ≤ values.length; rw [widthVal])
    (by change input.candidates.length - 0 ≤ _; omega)
    (by change self.hits.val + (matchingCandidates coefficients (input.candidates.val.drop 0)).length ≤ _; simpa [fresh] using rootCount)
  change (let result := (runChunks (prefixSlice locator (self.degree.val + 1)) self.degree.val
      input.candidates.length cursor self.hits.val workspace.roots values)
    result.1 = (matchingCandidates coefficients input.candidates.val).length ∧ result.2.2.2 = false)
  rw [locatorEq]
  simpa only [cursor, List.drop_zero, fresh, Nat.zero_add] using normal

/-- Fresh scanning of distinct candidates against an admitted monic locator
never encounters an excess root. It enters the original Deflation stage
with exact hit and root counters. -/
def ActualNativeCandidateNoOverhit : Prop :=
  ∀ {K : Type} (kernels : bulksketch.backend.contract.BulkKernels K bulksketch.field.Gf64),
    HornerLaw kernels →
    ∀ (self : Execution bulksketch.field.Gf64 K) (input : RowInput)
      (workspace : RowWorkspace) (meter : WorkMeter),
      CandidateEntryBounds self input workspace →
      self.hits.val = 0 →
      input.candidates.val.Nodup →
      let locator := prefixSlice workspace.bm (self.degree.val + 1)
      (slicePolynomial locator).Monic →
      (slicePolynomial locator).natDegree ≤ self.degree.val →
      let charge := StageCharge.chargeResult meter (candidateCost self.degree input.candidates.len)
      charge.1 = .Ok () →
      ∃ count roots scratch,
        Execution.candidates RootSetup.gf64Dictionary kernels self input workspace meter =
          .ok (.Ok (.Ok (some .Deflation)),
            { self with hits := count, roots := { self.roots with count := count } },
            candidateWorkspace input workspace roots scratch, id, charge.2) ∧
        count.val = (matchingCandidates locator input.candidates.val).length ∧ count.val ≤ self.degree.val

theorem native_candidate_no_overhit : ActualNativeCandidateNoOverhit := by
  intro K kernels horner self input workspace meter bounds fresh distinct
  dsimp only
  intro monic degreeBound paid
  have native := native_candidate_entry kernels horner self input workspace meter (fun _ => bounds)
  cases chargeEq : StageCharge.chargeResult meter (candidateCost self.degree input.candidates.len) with
  | mk status updatedMeter =>
    try rw [chargeEq] at native
    try rw [chargeEq] at paid
    change status = .Ok () at paid
    subst status
    obtain ⟨count, roots, scratch, reject, model, source, _, _, bound⟩ := native
    have complete := entry_complete self input workspace bounds fresh distinct monic degreeBound
    rw [model] at complete
    obtain ⟨total, noReject⟩ := complete
    change reject = false at noReject
    subst reject
    exact ⟨count, roots, scratch, source, total, bound⟩

#print axioms chunks_complete
#print axioms native_candidate_no_overhit

end BulksketchBridge.CandidateOuter
