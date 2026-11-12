import Arithmetic.CandidateOuterGenerated
import BulksketchBridge.CandidateInner
import BulksketchBridge.BmEntry
import BulksketchBridge.RootSetupSpec
import BulksketchBridge.ClosedLeafWindows
import BulksketchBridge.HornerPolynomial

namespace BulksketchBridge.CandidateOuter

open Aeneas Aeneas.Std Result ControlFlow
open BulksketchBridge.DenseCoefficient BulksketchBridge.RebuiltLfsr
open bulksketch.decode.stages.Execution
open Aeneas.Std.AvxHornerChunkRuntime (ChunkState window nextShared)

abbrev Reply := Nat × Slice U64 × Slice U64 × Bool

def evaluated (coefficients points : Slice U64) : Slice U64 :=
  Slice.from (points.val.map (PortableHornerChallenges.evalWord coefficients.val))
    (by simp)

@[simp] theorem evaluated_length (coefficients points : Slice U64) :
    (evaluated coefficients points).length = points.length := by
  simp only [evaluated, Slice.length, Slice.from_val, List.length_map]

/-- Every admitted backend uses the same GF64 word Horner fold on this
exactly sized destination. The original Dense method delegates directly. -/
def HornerLaw {K : Type} (kernels : bulksketch.backend.contract.BulkKernels K bulksketch.field.Gf64) : Prop :=
  ∀ coefficients points out : Slice U64, out.length = points.length →
    kernels.horner_many coefficients points out = .ok (evaluated coefficients points)

theorem portable_horner_call (coefficients points out : Slice U64) (width : out.length = points.length) :
    bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.horner_many
      RootSetup.gf64Dictionary coefficients points out = .ok (evaluated coefficients points) := by
  have behavior := PortableHorner.horner_many_refines coefficients points out
  dsimp only at behavior
  rw [ite_eq_left width] at behavior
  obtain ⟨written, exactCall, _, words⟩ := behavior
  rw [exactCall]
  congr 1
  apply Slice.ext
  simpa only [evaluated, Slice.from_val] using words

/-- The checked original Dense method delegates every result and mutation
to the supplied backend's original Horner operation. -/
def ActualNativeDenseEvalMany : Prop :=
  ∀ {F K : Type} (field : bulksketch.field.BinaryField F)
    (kernels : bulksketch.backend.contract.BulkKernels K F) (coefficients points out : Slice U64),
    bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial.eval_many_into field kernels coefficients points out =
      kernels.horner_many coefficients points out

theorem native_dense_eval_many : ActualNativeDenseEvalMany := by
  intro F K field kernels coefficients points out
  rfl

def chunkResult (coefficients points roots values : Slice U64) (degree hits : Nat) : Reply :=
  let scratch := restorePrefix values (evaluated coefficients points)
  let (count, written, reject) := CandidateInner.scan degree (List.zip points.val scratch.val) roots hits
  (count, written, scratch, reject)

def runChunks (coefficients : Slice U64) (degree : Nat) :
    Nat → ChunkState U64 → Nat → Slice U64 → Slice U64 → Reply
  | 0, _, hits, roots, values => (hits, roots, values, false)
  | fuel + 1, cursor, hits, roots, values =>
    if cursor.offset < cursor.words.length then
      let stop := min (cursor.offset + cursor.width) cursor.words.length
      let points := window cursor.words cursor.offset stop
      let (count, written, scratch, reject) := chunkResult coefficients points roots values degree hits
      if reject then (count, written, scratch, reject)
      else runChunks coefficients degree fuel { cursor with offset := stop } count written scratch
    else (hits, roots, values, false)

private theorem window_width (words : Slice U64) (start stop : Nat) (room : stop ≤ words.length) :
    (window words start stop).length = stop - start := by
  simp only [window, Slice.length, Slice.from_val, List.slice_length]
  exact Nat.min_eq_right (Nat.sub_le_sub_right room start)

private theorem chunk_step {K : Type}
    (kernels : bulksketch.backend.contract.BulkKernels K bulksketch.field.Gf64)
    (horner : HornerLaw kernels) (degree hits : Usize) (locator roots values : Slice U64)
    (cursor : ChunkState U64) (active : cursor.offset < cursor.words.length)
    (degreeRoom : degree.val < locator.length) (rootRoom : degree.val ≤ roots.length)
    (valid : hits.val ≤ degree.val) (valueRoom : cursor.width ≤ values.length) :
    let stop := min (cursor.offset + cursor.width) cursor.words.length
    let points := window cursor.words cursor.offset stop
    ∃ count written scratch reject,
      chunkResult (prefixSlice locator (degree.val + 1)) points roots values degree.val hits.val =
        (count.val, written, scratch, reject) ∧
      candidates_loop0.body RootSetup.gf64Dictionary kernels degree locator cursor hits roots values false =
        .ok (if reject then .done (count, written, scratch, reject)
          else .cont ({ cursor with offset := stop }, count, written, scratch, reject)) ∧
      written.length = roots.length ∧ scratch.length = values.length ∧ count.val ≤ degree.val := by
  dsimp only
  let stop := min (cursor.offset + cursor.width) cursor.words.length
  let points := window cursor.words cursor.offset stop
  let coeff := prefixSlice locator (degree.val + 1)
  let scratch := restorePrefix values (evaluated coeff points)
  have stopBound : stop ≤ cursor.words.length := Nat.min_le_right _ _
  have pointsLen : points.length = stop - cursor.offset := window_width _ _ _ stopBound
  have pointsRoom : points.length ≤ values.length := by
    have limit : stop ≤ cursor.offset + cursor.width := Nat.min_le_left _ _
    rw [pointsLen]
    omega
  have scratchLen : scratch.length = values.length := restore_length _ _
  have valuesRoom : points.length ≤ scratch.length := by rwa [scratchLen]
  have next : nextShared cursor = .ok (some points, { cursor with offset := stop }) := by
    simp only [nextShared, active, ite_true, points, stop]
  have exactLocator := ClosedLeaf.inclusive_prefix_normal locator degree degreeRoom
  have indexFrame := prefix_normal values points.len (by rw [Slice.len_val]; exact pointsRoom)
  rw [Slice.len_val] at indexFrame
  have width : (prefixSlice values points.length).length = points.length := by
    rw [prefix_length, Nat.min_eq_left pointsRoom]
  have ev := horner coeff points (prefixSlice values points.length) width
  obtain ⟨count, written, reject, modeled, native⟩ :=
    CandidateInner.native_candidate_inner points scratch roots degree hits 0 valuesRoom rootRoom valid
  simp only [List.drop_zero] at modeled
  have framed := CandidateInner.scan_frame degree.val (List.zip points.val scratch.val) roots hits.val rootRoom valid
  rw [modeled] at framed
  obtain ⟨_, countBound, rootLength, _, _⟩ := framed
  refine ⟨count, written, scratch, reject, ?_, ?_, rootLength, scratchLen, countBound⟩
  · change (let (h, r, b) := CandidateInner.scan degree.val (List.zip points.val scratch.val) roots hits.val
            (h, r, scratch, b)) = _
    rw [modeled]
  · unfold candidates_loop0.body
    simp only [next, bind_ok]
    dsimp! only
    rw [core.slice.index.Slice.index, exactLocator, bind_ok]
    simp only [core.slice.index.Slice.index_mut,
      indexFrame, bind_ok]
    dsimp! only
    have dense :
        bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial.eval_many_into RootSetup.gf64Dictionary kernels
          (prefixSlice locator (degree.val + 1)) points (prefixSlice values points.length) =
            .ok (evaluated coeff points) := by rw [native_dense_eval_many]; exact ev
    rw [dense, bind_ok]
    simp only [core.slice.Slice.iter, Aeneas.Std.core.iter.traits.iterator.Iterator.zip.trait_default,
      Aeneas.Std.core.iter.traits.iterator.Iterator.zip.default,
      core.iter.traits.collect.IntoIterator.Blanket.into_iter, bind_ok]
    have exactScan :
        candidates_loop0_loop0 ⟨⟨points, 0⟩, ⟨restorePrefix values (evaluated coeff points), 0⟩⟩
          degree hits roots false = .ok (count, written, reject) := native
    rw [exactScan, bind_ok]
    cases reject <;> rfl

/-- Original chunk cursor, both return classes, all written roots and the
complete values scratch after the last visited chunk. -/
def ActualNativeCandidateOuter : Prop :=
  ∀ {K : Type} (kernels : bulksketch.backend.contract.BulkKernels K bulksketch.field.Gf64),
    HornerLaw kernels →
    ∀ (degree hits : Usize) (locator roots values : Slice U64) (cursor : ChunkState U64) (fuel : Nat),
      degree.val < locator.length → degree.val ≤ roots.length → hits.val ≤ degree.val →
      0 < cursor.width → cursor.width ≤ values.length →
      cursor.words.length - cursor.offset ≤ fuel →
      ∃ count written scratch reject,
        runChunks (prefixSlice locator (degree.val + 1)) degree.val fuel cursor hits.val roots values =
          (count.val, written, scratch, reject) ∧
        candidates_loop0 RootSetup.gf64Dictionary kernels cursor degree hits roots locator values false =
          .ok (count, written, scratch, reject) ∧
        written.length = roots.length ∧ scratch.length = values.length ∧ count.val ≤ degree.val

private theorem end_chunk_run {K : Type}
    (kernels : bulksketch.backend.contract.BulkKernels K bulksketch.field.Gf64)
    (degree hits : Usize) (locator roots values : Slice U64) (cursor : ChunkState U64)
    (done : ¬ cursor.offset < cursor.words.length) :
    candidates_loop0 RootSetup.gf64Dictionary kernels cursor degree hits roots locator values false =
      .ok (hits, roots, values, false) := by
  have step : nextShared cursor = .ok (none, cursor) := by simp only [nextShared, done, ite_false]
  have body : candidates_loop0.body RootSetup.gf64Dictionary kernels degree locator cursor hits roots values false =
      .ok (.done (hits, roots, values, false)) := by
    simp only [candidates_loop0.body, step, bind_ok]
    rfl
  unfold candidates_loop0 loop
  dsimp only
  rw [body, bind_ok]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem native_candidate_outer : ActualNativeCandidateOuter := by
  intro K kernels horner degree hits locator roots values cursor fuel degreeRoom rootRoom valid positive valueRoom fits
  induction fuel generalizing hits roots values cursor with
  | zero =>
    have finished : ¬ cursor.offset < cursor.words.length := by omega
    exact ⟨hits, roots, values, false, rfl,
      end_chunk_run kernels degree hits locator roots values cursor finished, rfl, rfl, valid⟩
  | succ fuel ih =>
    by_cases active : cursor.offset < cursor.words.length
    · let stop := min (cursor.offset + cursor.width) cursor.words.length
      let points := window cursor.words cursor.offset stop
      let next : ChunkState U64 := { cursor with offset := stop }
      have advance : cursor.offset < stop := by
        unfold stop
        exact Nat.lt_min.mpr ⟨by omega, active⟩
      have nextFits : next.words.length - next.offset ≤ fuel := by
        change cursor.words.length - stop ≤ fuel
        omega
      obtain ⟨count, written, scratch, reject, modeled, source, rootsLen, scratchLen, countBound⟩ :=
        chunk_step kernels horner degree hits locator roots values cursor active degreeRoom rootRoom valid valueRoom
      change chunkResult (prefixSlice locator (degree.val + 1)) points roots values degree.val hits.val =
        (count.val, written, scratch, reject) at modeled
      change candidates_loop0.body RootSetup.gf64Dictionary kernels degree locator cursor hits roots values false =
        .ok (if reject then .done (count, written, scratch, reject)
          else .cont (next, count, written, scratch, reject)) at source
      cases reject with
      | false =>
        have nextPositive : 0 < next.width := positive
        have nextValueRoom : next.width ≤ scratch.length := by rw [scratchLen]; exact valueRoom
        obtain ⟨endCount, endRoots, endValues, endReject, laterModel, laterSource, rLen, vLen, endBound⟩ :=
          ih count written scratch next (by rwa [rootsLen]) countBound nextPositive nextValueRoom nextFits
        refine ⟨endCount, endRoots, endValues, endReject, ?_, ?_, rLen.trans rootsLen, vLen.trans scratchLen, endBound⟩
        · simp only [runChunks, active, ite_true]
          change (let (count, written, scratch, reject) :=
              chunkResult (prefixSlice locator (degree.val + 1)) points roots values degree.val hits.val
            if reject then (count, written, scratch, reject)
            else runChunks (prefixSlice locator (degree.val + 1)) degree.val fuel next count written scratch) = _
          rw [modeled]
          exact laterModel
        · simp only [Bool.false_eq_true, ite_false] at source
          unfold candidates_loop0 loop
          dsimp only
          rw [source, bind_ok]
          exact laterSource
      | true =>
        refine ⟨count, written, scratch, true, ?_, ?_, rootsLen, scratchLen, countBound⟩
        · simp only [runChunks, active, ite_true]
          change (let (count, written, scratch, reject) :=
              chunkResult (prefixSlice locator (degree.val + 1)) points roots values degree.val hits.val
            if reject then (count, written, scratch, reject)
            else runChunks (prefixSlice locator (degree.val + 1)) degree.val fuel next count written scratch) = _
          rw [modeled]
          rfl
        · simp only [ite_true] at source
          unfold candidates_loop0 loop
          dsimp only
          rw [source, bind_ok]
    · refine ⟨hits, roots, values, false, ?_,
        end_chunk_run kernels degree hits locator roots values cursor active, rfl, rfl, valid⟩
      simp only [runChunks, active, ite_false]

#print axioms native_candidate_outer

end BulksketchBridge.CandidateOuter
