import BulksketchBridge.RootTraceLoopSpec
import BulksketchBridge.ClosedLeafWindows
import BulksketchBridge.Algebra.Trace
import BulksketchBridge.DenseDivisionNormalized

namespace BulksketchBridge.RootTrace

open Aeneas Aeneas.Std Aeneas.Std.WP
open bulksketch.decode.roots bulksketch.backend.contract bulksketch.types
open DenseCoefficient SliceKernels Algebra.Gf64 Polynomial RebuiltLfsr

set_option maxRecDepth 4096
set_option maxHeartbeats 1400000

private theorem eval_remainder_at_root (p f : Polynomial Field) (x : Field)
    (root : f.IsRoot x) :
    (p %ₘ f).eval x = p.eval x := by
  change f.eval x = 0 at root
  have h := congrArg (Polynomial.eval x) (modByMonic_add_div p f)
  simpa only [eval_add, eval_mul, root, zero_mul, add_zero] using h

private theorem restored_prefix_length (trace replacement : Slice U64)
    (room : replacement.length ≤ trace.length) :
    prefixSlice (restorePrefix trace replacement) replacement.length = replacement := by
  apply Slice.ext
  have fits : replacement.val.length ≤ trace.val.length := room
  simp only [prefixSlice, restorePrefix, Slice.from_val, List.setSlice!, Nat.sub_zero, Nat.zero_add,
    List.take_zero, List.nil_append, Nat.min_eq_left fits, List.take_length]
  change (replacement.val ++ trace.val.drop replacement.val.length).take replacement.val.length = replacement.val
  rw [List.take_left]

private theorem restored_prefix (trace source : Slice U64) (len : Nat)
    (traceFits : len ≤ trace.length) (sourceFits : len ≤ source.length) :
    prefixSlice (restorePrefix trace (prefixSlice source len)) len = prefixSlice source len := by
  have length : (prefixSlice source len).length = len := by
    rw [prefix_length, Nat.min_eq_left sourceFits]
  simpa only [length] using
    restored_prefix_length trace (prefixSlice source len) (by rwa [length])

private theorem trace_body {K : Type} (square : RootTraceRuntime.ModularSquare)
    (backend : BulkKernels K bulksketch.field.Gf64) (range : core.ops.range.Range U32)
    (len : Usize) (modulus trace gcd table : Slice U64) (raw : Slice RawProduct) (splitter : U64)
    (active : range.start.val < range.«end».val) (room : 2 ≤ trace.length)
    (bounded : len.val ≤ trace.length) (gcdBound : trace.length ≤ gcd.length)
    (rawBound : 2 * trace.length < raw.length)
    (squareLaw : ModularSquareLaw square backend modulus table trace.length)
    (invariant : traceInvariant modulus splitter range.start.val len trace) :
    ∃ next out updated gcdOut rawOut,
      Roots.trace_loop1.body square gf64 backend modulus table splitter range len trace gcd raw =
        .ok (.cont (next, out, updated, gcdOut, rawOut)) ∧
      next.start.val = range.start.val + 1 ∧ next.«end» = range.«end» ∧
      out.val ≤ updated.length ∧ updated.length = trace.length ∧
      gcdOut.length = gcd.length ∧ rawOut.length = raw.length ∧
      traceInvariant modulus splitter next.start.val out updated ∧
      DenseGcd.Normal (prefixSlice updated out.val) := by
  obtain ⟨⟨option, next⟩, nextNormal, rfl, nextVal, nextEnd⟩ := RawMulTable.normal_of_spec _ _
    (core.iter.range.IteratorRange.next_U32_some_spec range active)
  have inputSize : (prefixSlice trace len.val).length ≤ trace.length := by
    rw [prefix_length]
    exact Nat.min_le_right _ _
  obtain ⟨size, gcdOut, rawOut, squareNormal, sizeBound, gcdLength, rawLength, squareMeaning⟩ :=
    squareLaw (prefixSlice trace len.val) gcd raw inputSize gcdBound rawBound
  have sourceFits : size.val ≤ gcdOut.length := by omega
  let copied := restorePrefix trace (prefixSlice gcdOut size.val)
  have copiedLength : copied.length = trace.length := restore_length _ _
  have sizeFits : size.val ≤ copied.length := by omega
  have oneFits : (1#usize).val < copied.length := by
    simp only [show (1#usize).val = 1 by decide, copiedLength]
    omega
  obtain ⟨out, updated, updateNormal, updatedLength, added, normalized⟩ :=
    xor_coefficient_polynomial_refines K backend copied size 1#usize splitter sizeFits oneFits
  have rawUpdate := xor_coefficient_refines gf64 backend copied size 1#usize splitter
  dsimp only at rawUpdate
  rw [ite_eq_left ⟨sizeFits, oneFits⟩] at rawUpdate
  obtain ⟨otherLength, other, rawNormal, _, _, lengthMeaning⟩ := rawUpdate
  have same := Result.ok_injective (rawNormal.symm.trans updateNormal)
  obtain ⟨sameLength, sameWords⟩ := Prod.mk.inj same
  subst otherLength
  subst other
  have outFits : out.val ≤ updated.length := by
    rw [lengthMeaning]
    exact (DenseNormalization.normalizedLength_le _).trans (by simp [Slice.length])
  have activeRoom : activeSize size.val (1#usize).val ≤ updated.length := by
    have := updatedLength
    unfold activeSize
    change max size.val 2 ≤ updated.length
    omega
  have lengthEq := (DenseDivision.normalized_value updated _ activeRoom).trans lengthMeaning.symm
  have normalPrefix := (DenseDivision.output_length_normal updated _ activeRoom).2
  rw [lengthEq] at normalPrefix
  have prefixLen : (prefixSlice updated out.val).length = out.val := by
    rw [prefix_length, Nat.min_eq_left outFits]
  have normalOutput : DenseGcd.Normal (prefixSlice updated out.val) := by
    intro positive
    rw [prefixLen] at positive ⊢
    exact normalPrefix positive
  have sharedInput := shared_prefix_normal trace len bounded
  have dest := prefix_normal trace size sizeBound
  have shared := shared_prefix_normal gcdOut size sourceFits
  have copy := ClosedLeaf.copy_normal (prefixSlice trace size.val) (prefixSlice gcdOut size.val)
    (by rw [prefix_length, prefix_length, Nat.min_eq_left sizeBound, Nat.min_eq_left sourceFits])
  refine ⟨next, out, updated, gcdOut, rawOut, ?_, nextVal, nextEnd, outFits,
    updatedLength.trans copiedLength, gcdLength, rawLength, ?_, normalOutput⟩
  · simp only [Roots.trace_loop1.body, nextNormal, bind_ok,
      Slice.index_SliceIndexRangeToUsizeSliceInst, sharedInput, squareNormal,
      Slice.index_mut_SliceIndexRangeToUsizeSliceInst, dest, shared]
    dsimp! only
    simp only [dest, shared, bind_ok]
    dsimp! only
    simp only [copy, bind_ok, show restorePrefix trace (prefixSlice gcdOut size.val) = copied from rfl,
      updateNormal]
    rfl
  · intro x root
    rw [normalized, added, show prefixSlice copied size.val = prefixSlice gcdOut size.val
      from restored_prefix trace gcdOut size.val sizeBound sourceFits, squareMeaning, eval_add,
      eval_remainder_at_root _ _ _ root, eval_pow, invariant x root, eval_monomial,
      show (1#usize).val = 1 by decide, pow_one, nextVal, traceAt]

theorem trace_loop_with_normal : ActualTraceLoopWithNormal := by
  intro square K backend range len modulus trace gcd table raw splitter positive ordered endpoint
    room bounded gcdBound rawBound squareLaw invariant
  suffices ∀ fuel (range : core.ops.range.Range U32) (len : Usize) (trace gcd : Slice U64)
      (raw : Slice RawProduct),
      1 ≤ range.start.val → range.start.val ≤ 64 → range.«end».val = 64 →
      2 ≤ trace.length → len.val ≤ trace.length → trace.length ≤ gcd.length →
      2 * trace.length < raw.length → 64 - range.start.val = fuel →
      ModularSquareLaw square backend modulus table trace.length →
      traceInvariant modulus splitter range.start.val len trace →
      ∃ output updated gcdOut rawOut,
        Roots.trace_loop1 square gf64 backend range len modulus trace gcd table raw splitter =
          .ok (output, updated, gcdOut, rawOut) ∧
        output.val ≤ updated.length ∧ updated.length = trace.length ∧
        gcdOut.length = gcd.length ∧ rawOut.length = raw.length ∧
        traceInvariant modulus splitter 64 output updated ∧
        (range.start.val < 64 ∨ DenseGcd.Normal (prefixSlice trace len.val) →
          DenseGcd.Normal (prefixSlice updated output.val))
    from this _ range len trace gcd raw positive ordered endpoint room bounded gcdBound rawBound rfl squareLaw invariant
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro range len trace gcd raw positive ordered endpoint room bounded gcdBound rawBound remaining squareLaw invariant
    by_cases active : range.start.val < range.«end».val
    · obtain ⟨next, out, updated, gcdOut, rawOut, step, nextVal, nextEnd, outFits,
        traceLength, gcdLength, rawLength, nextInvariant, nextNormal⟩ :=
        trace_body square backend range len modulus trace gcd table raw splitter active room bounded
          gcdBound rawBound squareLaw invariant
      have decrease : 64 - next.start.val < fuel := by omega
      obtain ⟨output, final, lastGcd, lastRaw, normal, finalFits, finalLength, lastGcdLength,
        lastRawLength, finalInvariant, finalNormalized⟩ := ih _ decrease next out updated gcdOut rawOut
          (by omega) (by omega) (by rw [nextEnd, endpoint]) (by omega) outFits (by omega) (by omega)
          rfl (by rwa [traceLength]) nextInvariant
      refine ⟨output, final, lastGcd, lastRaw, ?_, finalFits, finalLength.trans traceLength,
        lastGcdLength.trans gcdLength, lastRawLength.trans rawLength, finalInvariant, fun _ => finalNormalized (Or.inr nextNormal)⟩
      unfold Roots.trace_loop1 loop
      dsimp only
      simp only [step, bind_ok]
      exact normal
    · have atEnd : range.start.val = 64 := by omega
      obtain ⟨⟨option, unchanged⟩, nextNormal, rfl, rfl⟩ := RawMulTable.normal_of_spec _ _
        (core.iter.range.IteratorRange.next_U32_none_spec range (by omega))
      refine ⟨len, trace, gcd, raw, ?_, bounded, rfl, rfl, rfl, by simpa only [atEnd] using invariant, ?_⟩
      · unfold Roots.trace_loop1 loop
        dsimp only
        have terminal :
            Roots.trace_loop1.body square gf64 backend modulus table splitter unchanged len trace gcd raw =
              .ok (.done (len, trace, gcd, raw)) := by
          simp only [Roots.trace_loop1.body, nextNormal, bind_ok]
          rfl
        rw [terminal]
        simp only [bind_ok]
      · exact fun h => h.resolve_left (by omega)

theorem trace_loop_refines : ActualTraceLoop := by
  intro square K backend range len modulus trace gcd table raw splitter positive ordered endpoint
    room bounded gcdBound rawBound squareLaw invariant
  obtain ⟨output, updated, gcdOut, rawOut, ran, size, traceWidth, gcdWidth, rawWidth, meaning, _⟩ :=
    trace_loop_with_normal square backend range len modulus trace gcd table raw splitter positive ordered
      endpoint room bounded gcdBound rawBound squareLaw invariant
  exact ⟨output, updated, gcdOut, rawOut, ran, size, traceWidth, gcdWidth, rawWidth, meaning⟩

end BulksketchBridge.RootTrace
