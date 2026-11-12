import BulksketchBridge.CandidateEntry

namespace BulksketchBridge.CandidateOuter

open Aeneas.Std Algebra.Gf64 SliceKernels
open BulksketchBridge.RebuiltLfsr
open Aeneas.Std.AvxHornerChunkRuntime (ChunkState window)

private def selected (coefficients : Slice U64) (words : List U64) : List U64 :=
  words.filter (fun word => decide (PortableHornerChallenges.evalWord coefficients.val word = 0#u64))

private theorem zipped_zero (coefficients : Slice U64) (words suffix : List U64) :
    CandidateInner.zeroPoints
        (List.zip words (words.map (PortableHornerChallenges.evalWord coefficients.val) ++ suffix)) =
      selected coefficients words := by
  induction words with
  | nil => rfl
  | cons head tail ih =>
    by_cases zero : PortableHornerChallenges.evalWord coefficients.val head = 0#u64
    · simp only [selected, List.map_cons, List.cons_append, List.zip_cons_cons,
        CandidateInner.zeroPoints, zero, ite_true, decide_true, List.filter_cons_of_pos]
      rw [ih]
      rfl
    · simp only [selected, List.map_cons, List.cons_append, List.zip_cons_cons,
        CandidateInner.zeroPoints, zero, ite_false, decide_false, List.filter_cons, Bool.false_eq_true]
      exact ih

private theorem evaluated_prefix (coefficients points values : Slice U64)
    (room : points.length ≤ values.length) :
    (restorePrefix values (evaluated coefficients points)).val =
      points.val.map (PortableHornerChallenges.evalWord coefficients.val) ++ values.val.drop points.length := by
  change points.val.length ≤ values.val.length at room
  simp only [restorePrefix, evaluated, Slice.from_val, List.setSlice!, List.take_zero,
    Nat.sub_zero, Nat.zero_add, List.nil_append, List.length_map, Nat.min_eq_left room]
  rw [List.take_of_length_le (by simp)]

/-- Candidate outputs are an ordered sublist of the source candidates.
The exact output interval contains only roots of the supplied locator. -/
def SupportFrame (coefficients : Slice U64) (degree : Nat) (input : List U64)
    (roots : Slice U64) (hits : Nat) (result : Reply) : Prop :=
  ∃ accepted,
    accepted.Sublist input ∧
    result.1 = hits + accepted.length ∧ result.1 ≤ degree ∧
    result.2.1.length = roots.length ∧
    result.2.1.val =
      roots.val.take hits ++ accepted ++ roots.val.drop (hits + accepted.length) ∧
    ∀ point ∈ accepted, (slicePolynomial coefficients).IsRoot (toField point.bv)

private theorem chunk_support (coefficients points roots values : Slice U64) (degree hits : Nat)
    (rootRoom : degree ≤ roots.length) (valid : hits ≤ degree) (room : points.length ≤ values.length) :
    SupportFrame coefficients degree points.val roots hits
      (chunkResult coefficients points roots values degree hits) := by
  let scratch := restorePrefix values (evaluated coefficients points)
  have matched : CandidateInner.zeroPoints (List.zip points.val scratch.val) =
      selected coefficients points.val := by
    rw [show scratch.val = _ from evaluated_prefix coefficients points values room]
    exact zipped_zero _ _ _
  have scanned := CandidateInner.scan_frame degree (List.zip points.val scratch.val) roots hits rootRoom valid
  simp only [CandidateInner.ScanFrame, matched] at scanned
  obtain ⟨count, bound, length, output, _⟩ := scanned
  let accepted := (selected coefficients points.val).take (degree - hits)
  have fromRoots : accepted.Sublist (selected coefficients points.val) := List.take_sublist _ _
  refine ⟨accepted, fromRoots.trans List.filter_sublist, ?_, ?_, ?_, ?_, ?_⟩
  · exact count
  · exact bound
  · exact length
  · exact output
  · intro point member
    have inFilter := List.mem_filter.mp (fromRoots.subset member)
    have zero : PortableHornerChallenges.evalWord coefficients.val point = 0#u64 :=
      of_decide_eq_true inFilter.2
    change (slicePolynomial coefficients).eval (toField point.bv) = 0
    rw [← PortableHorner.horner_word_evaluates, zero]
    exact toField_zero

private theorem patch_compose (initial middle final : List U64)
    (first second : List U64) (hits : Nat) (room : hits ≤ initial.length)
    (one : middle = initial.take hits ++ first ++ initial.drop (hits + first.length))
    (two : final = middle.take (hits + first.length) ++ second ++
      middle.drop (hits + first.length + second.length)) :
    final = initial.take hits ++ (first ++ second) ++
      initial.drop (hits + (first ++ second).length) := by
  have width : (initial.take hits ++ first).length = hits + first.length := by
    simp only [List.length_append, List.length_take, Nat.min_eq_left room]
  have take : middle.take (hits + first.length) = initial.take hits ++ first := by
    rw [one, ← width, List.take_left]
  have drop : middle.drop (hits + first.length) = initial.drop (hits + first.length) := by
    conv_lhs => rw [one, ← width, List.drop_left]
    rw [width]
  rw [two, take, ← List.drop_drop (i := second.length) (j := hits + first.length), drop, List.drop_drop,
    List.length_append]
  simp only [List.append_assoc, Nat.add_assoc]

private theorem empty_support (coefficients : Slice U64) (degree : Nat) (input : List U64)
    (roots : Slice U64) (values : Slice U64) (hits : Nat) (valid : hits ≤ degree) :
    SupportFrame coefficients degree input roots hits (hits, roots, values, false) := by
  refine ⟨[], List.nil_sublist _, by simp, valid, rfl, ?_, by simp⟩
  simp only [List.length_nil, Nat.add_zero, List.append_nil, List.take_append_drop]

/-- Every chunk contributes an ordered sublist of the original candidates.
Previously accepted words and the untouched output suffix are preserved. -/
theorem chunks_support (coefficients : Slice U64) (degree fuel : Nat) (cursor : ChunkState U64)
    (hits : Nat) (roots values : Slice U64)
    (rootRoom : degree ≤ roots.length) (valid : hits ≤ degree)
    (width : cursor.width ≤ values.length) :
    SupportFrame coefficients degree (cursor.words.val.drop cursor.offset) roots hits
      (runChunks coefficients degree fuel cursor hits roots values) := by
  induction fuel generalizing cursor hits roots values with
  | zero => exact empty_support _ _ _ _ _ _ valid
  | succ fuel ih =>
    by_cases active : cursor.offset < cursor.words.length
    · let stop := min (cursor.offset + cursor.width) cursor.words.length
      let points := window cursor.words cursor.offset stop
      have offsetStop : cursor.offset ≤ stop := by
        unfold stop
        exact Nat.le_min.mpr ⟨by omega, active.le⟩
      have stopBound : stop ≤ cursor.words.length := Nat.min_le_right _ _
      have pointsLength : points.length = stop - cursor.offset := by
        simp only [points, window, Slice.length, Slice.from_val, List.slice_length]
        exact Nat.min_eq_right (Nat.sub_le_sub_right stopBound _)
      have pointRoom : points.length ≤ values.length := by
        have stopWidth : stop ≤ cursor.offset + cursor.width := Nat.min_le_left _ _
        omega
      have pointList : points.val = (cursor.words.val.drop cursor.offset).take (stop - cursor.offset) := by
        simp only [points, window, Slice.from_val, List.slice]
      have remaining : (cursor.words.val.drop cursor.offset).drop (stop - cursor.offset) =
          cursor.words.val.drop stop := by
        rw [List.drop_drop, Nat.add_sub_of_le offsetStop]
      have partition : points.val ++ cursor.words.val.drop stop = cursor.words.val.drop cursor.offset := by
        rw [pointList, ← remaining, List.take_append_drop]
      have framed := chunk_support coefficients points roots values degree hits rootRoom valid pointRoom
      obtain ⟨count, written, scratch, reject, stepped⟩ :
          ∃ count written scratch reject,
            chunkResult coefficients points roots values degree hits = (count, written, scratch, reject) := by
        exact ⟨_, _, _, _, Prod.eta _ |>.symm.trans (by rfl)⟩
      rw [stepped] at framed
      obtain ⟨first, fromChunk, counted, bound, rootLength, firstFrame, firstRoots⟩ := framed
      change count = hits + first.length at counted
      change written.length = roots.length at rootLength
      have scratchLength : scratch.length = values.length := by
        have projected := congrArg (fun answer : Reply => answer.2.2.1.length) stepped
        change (restorePrefix values (evaluated coefficients points)).length = scratch.length at projected
        rw [← projected, restore_length]
      simp only [runChunks, active, ite_true]
      change SupportFrame coefficients degree (cursor.words.val.drop cursor.offset) roots hits
        (let (n, r, v, reject) := chunkResult coefficients points roots values degree hits
         if reject then (n, r, v, reject)
         else runChunks coefficients degree fuel { cursor with offset := stop } n r v)
      rw [stepped]
      cases reject with
      | true =>
        simp only [ite_true]
        refine ⟨first, fromChunk.trans ?_, counted, bound, rootLength, firstFrame, firstRoots⟩
        rw [pointList]
        exact List.take_sublist _ _
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        have tailWidth : ({ cursor with offset := stop } : ChunkState U64).width ≤ scratch.length := by
          rw [scratchLength]
          exact width
        obtain ⟨second, fromRest, total, finalBound, finalLength, secondFrame, secondRoots⟩ :=
          ih { cursor with offset := stop } count written scratch (by rwa [rootLength]) bound tailWidth
        refine ⟨first ++ second, ?_, ?_, finalBound, finalLength.trans rootLength, ?_, ?_⟩
        · exact partition ▸ fromChunk.append fromRest
        · simp only [List.length_append]
          rw [total, counted, Nat.add_assoc]
        · apply patch_compose roots.val written.val _ first second hits (valid.trans rootRoom) firstFrame
          simpa only [counted] using secondFrame
        · intro point member
          rcases List.mem_append.mp member with member | member
          · exact firstRoots point member
          · exact secondRoots point member
    · simp only [runChunks, active, ite_false]
      exact empty_support _ _ _ _ _ _ valid

open DenseCoefficient BmEntry
open bulksketch.decode.stages bulksketch.decode.row bulksketch.decode.scratch bulksketch.types

theorem entry_model_support {K : Type} (self : Execution bulksketch.field.Gf64 K)
    (input : RowInput) (workspace : RowWorkspace) (bounds : CandidateEntryBounds self input workspace) :
    SupportFrame (prefixSlice workspace.bm (self.degree.val + 1)) self.degree.val
      input.candidates.val workspace.roots self.hits.val (candidateEntryModel self input workspace) := by
  obtain ⟨degreeRoom, buffers, rootRoom, valid⟩ := bounds
  let width := input.difference.length + 1
  let locator := prefixSlice workspace.bm width
  let values := prefixSlice (tail workspace.bm width) width
  let cursor : ChunkState U64 := ⟨input.candidates, 0, width⟩
  have valuesLen : values.length = width := by
    unfold values
    rw [prefix_length, tail_length, Nat.min_eq_left (by omega)]
  have locatorEq : prefixSlice locator (self.degree.val + 1) =
      prefixSlice workspace.bm (self.degree.val + 1) := by
    apply Slice.ext
    simp only [locator, prefixSlice, Slice.from_val, List.take_take]
    rw [Nat.min_eq_left (by omega : self.degree.val + 1 ≤ width)]
  have frame := chunks_support (prefixSlice locator (self.degree.val + 1)) self.degree.val
    input.candidates.length cursor self.hits.val workspace.roots values rootRoom valid
    (by change width ≤ values.length; rw [valuesLen])
  change SupportFrame (prefixSlice locator (self.degree.val + 1)) self.degree.val
    (input.candidates.val.drop 0) workspace.roots self.hits.val (candidateEntryModel self input workspace) at frame
  simpa only [locatorEq, List.drop_zero] using frame

/-- With a distinct candidate input, every newly accepted word is distinct
and is a root of the actual locator. When the source enters with zero hits,
these words are exactly the full returned roots prefix. -/
def ActualNativeCandidateDistinct : Prop :=
  ∀ {K : Type} (kernels : bulksketch.backend.contract.BulkKernels K bulksketch.field.Gf64),
    HornerLaw kernels →
    ∀ (self : Execution bulksketch.field.Gf64 K) (input : RowInput)
      (workspace : RowWorkspace) (meter : WorkMeter),
      CandidateEntryBounds self input workspace →
      input.candidates.val.Nodup →
      let charge := StageCharge.chargeResult meter (candidateCost self.degree input.candidates.len)
      charge.1 = .Ok () →
      ∃ count roots scratch reject accepted,
        Execution.candidates RootSetup.gf64Dictionary kernels self input workspace meter =
          .ok (completedReply reject, completedExecution self count reject,
            candidateWorkspace input workspace roots scratch, id, charge.2) ∧
        accepted.Sublist input.candidates.val ∧ accepted.Nodup ∧
        count.val = self.hits.val + accepted.length ∧
        roots.val = workspace.roots.val.take self.hits.val ++ accepted ++ workspace.roots.val.drop count.val ∧
        (self.hits.val = 0 → roots.val.take count.val = accepted) ∧
        ∀ point ∈ accepted,
          (slicePolynomial (prefixSlice workspace.bm (self.degree.val + 1))).IsRoot (toField point.bv)

theorem native_candidate_distinct : ActualNativeCandidateDistinct := by
  intro K kernels horner self input workspace meter bounds distinct
  dsimp only
  intro paid
  have native := native_candidate_entry kernels horner self input workspace meter (fun _ => bounds)
  cases chargeEq : StageCharge.chargeResult meter (candidateCost self.degree input.candidates.len) with
  | mk status updatedMeter =>
    try rw [chargeEq] at native
    try rw [chargeEq] at paid
    change status = .Ok () at paid
    subst status
    obtain ⟨count, roots, scratch, reject, model, source, _, _, _⟩ := native
    have frame := entry_model_support self input workspace bounds
    rw [model] at frame
    obtain ⟨accepted, sublist, counted, _, _, frame, members⟩ := frame
    change count.val = self.hits.val + accepted.length at counted
    change roots.val = workspace.roots.val.take self.hits.val ++ accepted ++
      workspace.roots.val.drop (self.hits.val + accepted.length) at frame
    rw [← counted] at frame
    refine ⟨count, roots, scratch, reject, accepted, source, sublist, sublist.nodup distinct,
      counted, frame, ?_, members⟩
    intro fresh
    have countLength : count.val = accepted.length := by rw [counted, fresh, Nat.zero_add]
    rw [frame, fresh, List.take_zero, List.nil_append, countLength, List.take_left]

#print axioms chunks_support
#print axioms native_candidate_distinct

end BulksketchBridge.CandidateOuter
