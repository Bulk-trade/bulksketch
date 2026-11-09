import BulksketchBridge.RootTraceWrapperSpec
import BulksketchBridge.RootTraceBasis
import BulksketchBridge.RootTraceField
import BulksketchBridge.ReconstructionLoop
import BulksketchBridge.ClosedLeafAdvance
import BulksketchBridge.BmPrice

namespace BulksketchBridge.RootTrace

open Aeneas Aeneas.Std Aeneas.Std.WP
open DenseCoefficient SliceKernels Algebra.Gf64 Polynomial RebuiltLfsr FrobeniusTables
open bulksketch.decode.roots bulksketch.backend.contract bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

private theorem cache_ready {K : Type} (backend : BulkKernels K bulksketch.field.Gf64)
    (self : Roots) (buffers : FactorWork) (ready : cacheWellFormed self buffers) :
    ∃ length basis,
      RootTraceRuntime.getOrInsertWith
        (Roots.trace.closure.Insts.CoreOpsFunctionFnOnceTupleArrayU6464 gf64 backend)
        buffers.basis.directions (self.splitter_seed, buffers.basis.len) =
          .ok (basis, some, (self.splitter_seed, length)) ∧
      1 ≤ length.val ∧ length.val ≤ 64 ∧ cachePrefix self.splitter_seed basis length.val ∧
      length.val = cacheInitialLength buffers := by
  cases cached : buffers.basis.directions with
  | none =>
    let fresh := (Array.repeat 64#usize 0#u64).set 0#usize (basisSeed self.splitter_seed)
    obtain ⟨normal, correct⟩ := seed_closure_refines backend self.splitter_seed buffers.basis.len
    refine ⟨1#u32, fresh, ?_, by decide, by decide, ?_⟩
    · change Aeneas.Std.bind
        (Roots.trace.closure.Insts.CoreOpsFunctionFnOnceTupleArrayU6464.call_once
          gf64 backend (self.splitter_seed, buffers.basis.len) ()) _ = _
      rw [normal, bind_ok]
      rfl
    · exact ⟨correct, by simp [cacheInitialLength, cached]⟩
  | some basis =>
    obtain ⟨positive, width, correct⟩ := ready basis cached
    refine ⟨buffers.basis.len, basis, ?_, positive, width, correct, by simp [cacheInitialLength, cached]⟩
    rfl

private def traceStart (trace : Slice U64) (splitter : U64) : Slice U64 :=
  (zeroWords trace).setAtNat 1 splitter

private theorem trace_start_length (trace : Slice U64) (splitter : U64) :
    (traceStart trace splitter).length = trace.length := by
  simp [traceStart, zeroWords, Slice.length]

private theorem trace_start_invariant (modulus trace : Slice U64) (splitter : U64)
    (room : 2 ≤ trace.length) :
    traceInvariant modulus splitter 1 2#usize (traceStart trace splitter) := by
  have bounded : 2 ≤ (traceStart trace splitter).length := by rwa [trace_start_length]
  have entry0 : (traceStart trace splitter)[(0 : Nat)]! = 0#u64 := by
    rw [traceStart, Slice.getElem!_Nat_eq, Slice.getElem!_Nat_setAtNat_ne _ 1 0 _ (by decide)]
    simp [zeroWords, show 0 < trace.length by omega]
  have entry1 : (traceStart trace splitter)[(1 : Nat)]! = splitter := by
    rw [traceStart, Slice.getElem!_Nat_eq, Slice.getElem!_Nat_setAtNat_eq]
    simp [zeroWords, show 1 < trace.length by omega]
  have poly : slicePolynomial (prefixSlice (traceStart trace splitter) 2) = monomial 1 (toField splitter.bv) := by
    ext i
    rw [prefix_coeff _ _ _ bounded, coeff_monomial]
    by_cases first : i = 0
    · subst i
      simp [entry0]
      exact toField_zero
    · by_cases second : i = 1
      · subst i
        simp [entry1]
      · simp [show ¬ i < 2 by omega, second, Ne.symm second]
  intro x _
  change (slicePolynomial (prefixSlice (traceStart trace splitter) 2)).eval x = _
  simp [poly, eval_monomial, traceAt]

theorem trace_charge_failure (square : RootTraceRuntime.ModularSquare) {K : Type}
    (backend : BulkKernels K bulksketch.field.Gf64) (self : Roots) (buffers : FactorWork)
    (meter finalMeter : WorkMeter) (failure : DecodeError)
    (charged : bulksketch.decode.roots.charge meter (.Trace self.degree) = .ok (.Err failure, finalMeter)) :
    Roots.trace square gf64 backend self buffers meter = .ok (.Err failure, self, buffers, id, finalMeter) := by
  simp only [Roots.trace, charged, bind_ok]
  dsimp! only
  simp [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
  rfl

/-- The complete already-checked branch preserves the paid meter and every
FactorWork field outside the original cache, trace, GCD and raw writes. -/
theorem trace_checked_refines (square : RootTraceRuntime.ModularSquare) {K : Type}
    (backend : BulkKernels K bulksketch.field.Gf64) (self : Roots) (buffers : FactorWork)
    (meter paidMeter : WorkMeter)
    (charged : bulksketch.decode.roots.charge meter (.Trace self.degree) = .ok (.Ok (), paidMeter))
    (checked : self.checked = true) (counterFits : self.attempts.val + 1 ≤ Usize.max)
    (directionFits : self.direction.val < 64) (cached : cacheWellFormed self buffers)
    (traceFits : 2 ≤ buffers.trace.length) (gcdFits : buffers.trace.length ≤ buffers.gcd.length)
    (rawFits : 2 * buffers.trace.length < buffers.raw.length)
    (squareLaw : ModularSquareLaw square backend buffers.modulus buffers.table buffers.trace.length) :
    ∃ attempts length basis lengthOut traceOut gcdOut rawOut,
      Roots.trace square gf64 backend self buffers meter =
        .ok (.Ok (.Ok .Gcd), { self with attempts, trace_len := lengthOut },
          { buffers with trace := traceOut, gcd := gcdOut, raw := rawOut, basis := ⟨some basis, length⟩ }, id, paidMeter) ∧
      attempts.val = self.attempts.val + 1 ∧
      self.direction.val < length.val ∧
      length.val = max (cacheInitialLength buffers) (self.direction.val + 1) ∧
      length.val ≤ 64 ∧ cachePrefix self.splitter_seed basis length.val ∧
      lengthOut.val ≤ traceOut.length ∧ traceOut.length = buffers.trace.length ∧
      gcdOut.length = buffers.gcd.length ∧ rawOut.length = buffers.raw.length ∧
      traceInvariant buffers.modulus (basisWord self.splitter_seed self.direction.val) 64 lengthOut traceOut := by
  obtain ⟨attempts, attemptNormal, attemptVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := self.attempts) (y := 1#usize) (by exact counterFits))
  obtain ⟨oldLength, oldBasis, getNormal, positive, width, cacheCorrect, oldExact⟩ :=
    cache_ready backend self buffers cached
  obtain ⟨length, basis, extendNormal, lengthVal, finalCorrect, _⟩ :=
    basis_extension_refines self.splitter_seed self.direction oldLength oldBasis directionFits positive width cacheCorrect
  have directionLive : self.direction.val < length.val := by
    rw [lengthVal]
    exact Nat.lt_of_succ_le (Nat.le_max_right _ _)
  have exactBasisLength : length.val = max (cacheInitialLength buffers) (self.direction.val + 1) := by
    rw [lengthVal, oldExact]
  have finalWidth : length.val ≤ 64 := by rw [lengthVal]; exact max_le width (by omega)
  let splitter := basisWord self.splitter_seed self.direction.val
  have read := read_normal basis (UScalar.cast .Usize self.direction)
    (by rw [U32.cast_Usize_val_eq]; exact directionFits)
  rw [U32.cast_Usize_val_eq, finalCorrect _ directionLive] at read
  have startLen := trace_start_length buffers.trace splitter
  have fill := fill_zero buffers.trace
  have zeroLen : (zeroWords buffers.trace).length = buffers.trace.length := by simp [zeroWords, Slice.length]
  have update := Reconstruction.update_normal (zeroWords buffers.trace) 1#usize splitter
    (by change (1#usize).val < (zeroWords buffers.trace).length; rw [zeroLen]
        exact Nat.lt_of_succ_le traceFits)
  let range : core.ops.range.Range U32 := ⟨1#u32, 64#u32⟩
  obtain ⟨out, traceOut, gcdOut, rawOut, loopNormal, outFits, traceLen, gcdLen, rawLen, correct⟩ :=
    trace_loop_refines square backend range 2#usize buffers.modulus (traceStart buffers.trace splitter)
      buffers.gcd buffers.table buffers.raw splitter (by decide) (by decide) (by decide)
      (by rwa [startLen]) (by change 2 ≤ _; rwa [startLen]) (by rwa [startLen]) (by rwa [startLen])
      (by rwa [startLen]) (trace_start_invariant _ _ _ traceFits)
  refine ⟨attempts, length, basis, out, traceOut, gcdOut, rawOut, ?_, ?_, directionLive, exactBasisLength, finalWidth, finalCorrect,
    outFits, traceLen.trans startLen, gcdLen, rawLen, correct⟩
  · simp only [Roots.trace, charged, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
    dsimp! only
    simp only [attemptNormal, getNormal, bind_ok]
    dsimp! only
    have bits : gf64.BITS = Result.ok 64#u32 := by
      change Result.ok bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS = _
      rw [bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS]
    simp only [extendNormal, bind_ok]
    dsimp! only
    simp only [lift, read, fill, update, bind_ok, bits,
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS,
      show (1#usize).val = 1 by decide,
      show basisWord self.splitter_seed self.direction.val = splitter from rfl,
      show (zeroWords buffers.trace).setAtNat 1 splitter = traceStart buffers.trace splitter from rfl,
      show ({ start := 1#u32, «end» := 64#u32 } : core.ops.range.Range U32) = range from rfl,
      loopNormal, checked, ite_true]
    rfl
  · exact attemptVal

theorem trace_split_charge_failure (square : RootTraceRuntime.ModularSquare) {K : Type}
    (backend : BulkKernels K bulksketch.field.Gf64) (self : Roots) (buffers : FactorWork)
    (meter paidMeter failedMeter : WorkMeter) (failure : DecodeError)
    (charged : bulksketch.decode.roots.charge meter (.Trace self.degree) = .ok (.Ok (), paidMeter))
    (splitFailed : bulksketch.decode.roots.charge paidMeter (.SplitCheck self.degree) =
      .ok (.Err failure, failedMeter))
    (checked : self.checked = false) (counterFits : self.attempts.val + 1 ≤ Usize.max)
    (directionFits : self.direction.val < 64) (cached : cacheWellFormed self buffers)
    (traceFits : 2 ≤ buffers.trace.length) (gcdFits : buffers.trace.length ≤ buffers.gcd.length)
    (rawFits : 2 * buffers.trace.length < buffers.raw.length)
    (squareLaw : ModularSquareLaw square backend buffers.modulus buffers.table buffers.trace.length) :
    ∃ attempts length basis lengthOut traceOut gcdOut rawOut,
      Roots.trace square gf64 backend self buffers meter =
        .ok (.Err failure, { self with attempts, trace_len := lengthOut },
          { buffers with trace := traceOut, gcd := gcdOut, raw := rawOut, basis := ⟨some basis, length⟩ }, id, failedMeter) ∧
      attempts.val = self.attempts.val + 1 ∧
      self.direction.val < length.val ∧
      length.val = max (cacheInitialLength buffers) (self.direction.val + 1) ∧
      length.val ≤ 64 ∧ cachePrefix self.splitter_seed basis length.val ∧
      lengthOut.val ≤ traceOut.length ∧ traceOut.length = buffers.trace.length ∧
      gcdOut.length = buffers.gcd.length ∧ rawOut.length = buffers.raw.length ∧
      traceInvariant buffers.modulus (basisWord self.splitter_seed self.direction.val) 64 lengthOut traceOut := by
  obtain ⟨attempts, attemptNormal, attemptVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := self.attempts) (y := 1#usize) (by exact counterFits))
  obtain ⟨oldLength, oldBasis, getNormal, positive, width, cacheCorrect, oldExact⟩ :=
    cache_ready backend self buffers cached
  obtain ⟨length, basis, extendNormal, lengthVal, finalCorrect, _⟩ :=
    basis_extension_refines self.splitter_seed self.direction oldLength oldBasis directionFits positive width cacheCorrect
  have directionLive : self.direction.val < length.val := by
    rw [lengthVal]
    exact Nat.lt_of_succ_le (Nat.le_max_right _ _)
  have exactBasisLength : length.val = max (cacheInitialLength buffers) (self.direction.val + 1) := by
    rw [lengthVal, oldExact]
  have finalWidth : length.val ≤ 64 := by rw [lengthVal]; exact max_le width (by omega)
  let splitter := basisWord self.splitter_seed self.direction.val
  have read := read_normal basis (UScalar.cast .Usize self.direction)
    (by rw [U32.cast_Usize_val_eq]; exact directionFits)
  rw [U32.cast_Usize_val_eq, finalCorrect _ directionLive] at read
  have startLen := trace_start_length buffers.trace splitter
  have fill := fill_zero buffers.trace
  have zeroLen : (zeroWords buffers.trace).length = buffers.trace.length := by simp [zeroWords, Slice.length]
  have update := Reconstruction.update_normal (zeroWords buffers.trace) 1#usize splitter
    (by change (1#usize).val < (zeroWords buffers.trace).length; rw [zeroLen]
        exact Nat.lt_of_succ_le traceFits)
  let range : core.ops.range.Range U32 := ⟨1#u32, 64#u32⟩
  obtain ⟨out, traceOut, gcdOut, rawOut, loopNormal, outFits, traceLen, gcdLen, rawLen, correct⟩ :=
    trace_loop_refines square backend range 2#usize buffers.modulus (traceStart buffers.trace splitter)
      buffers.gcd buffers.table buffers.raw splitter (by decide) (by decide) (by decide)
      (by rwa [startLen]) (by change 2 ≤ _; rwa [startLen]) (by rwa [startLen]) (by rwa [startLen])
      (by rwa [startLen]) (trace_start_invariant _ _ _ traceFits)
  refine ⟨attempts, length, basis, out, traceOut, gcdOut, rawOut, ?_, ?_, directionLive, exactBasisLength, finalWidth, finalCorrect,
    outFits, traceLen.trans startLen, gcdLen, rawLen, correct⟩
  · simp only [Roots.trace, charged, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
    dsimp! only
    simp only [attemptNormal, getNormal, bind_ok]
    dsimp! only
    have bits : gf64.BITS = Result.ok 64#u32 := by
      change Result.ok bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS = _
      rw [bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS]
    simp only [extendNormal, bind_ok]
    dsimp! only
    simp only [lift, read, fill, update, bind_ok, bits,
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS,
      show (1#usize).val = 1 by decide,
      show basisWord self.splitter_seed self.direction.val = splitter from rfl,
      show (zeroWords buffers.trace).setAtNat 1 splitter = traceStart buffers.trace splitter from rfl,
      show ({ start := 1#u32, «end» := 64#u32 } : core.ops.range.Range U32) = range from rfl,
      loopNormal, checked, Bool.false_eq_true, ite_false, splitFailed]
    dsimp! only
    simp only [Bind.bind, bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
    rfl
  · exact attemptVal

private theorem slice_ne (left right : Slice U64) :
    core.cmp.PartialEq.ne.trait_default
      (bulksketch.Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU64) left right =
      Result.ok (decide (left ≠ right)) := by
  have proof := core.cmp.PartialEq.ne.trait_default.spec
    (bulksketch.Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU64) left right (by
      apply core.slice.cmp.PartialEqSlice.eq_homo_spec
      intro x y
      change WP.spec (Result.ok (decide (x ≠ y))) _
      simp only [spec_ok, decide_eq_true_eq])
  obtain ⟨result, normal, meaning⟩ := RawMulTable.normal_of_spec _ _ proof
  have exactResult : result = decide (left ≠ right) := by
    apply Bool.eq_iff_iff.mpr
    simpa using meaning
  exact normal.trans (congrArg Result.ok exactResult)

theorem trace_split_checked_evidence (square : RootTraceRuntime.ModularSquare) {K : Type}
    (backend : BulkKernels K bulksketch.field.Gf64) (self : Roots) (buffers : FactorWork)
    (meter paidMeter splitMeter : WorkMeter)
    (charged : bulksketch.decode.roots.charge meter (.Trace self.degree) = .ok (.Ok (), paidMeter))
    (splitPaid : bulksketch.decode.roots.charge paidMeter (.SplitCheck self.degree) =
      .ok (.Ok (), splitMeter))
    (degreeFits : self.degree.val ≤ buffers.gcd.length)
    (checked : self.checked = false) (counterFits : self.attempts.val + 1 ≤ Usize.max)
    (directionFits : self.direction.val < 64) (cached : cacheWellFormed self buffers)
    (traceFits : 2 ≤ buffers.trace.length) (gcdFits : buffers.trace.length ≤ buffers.gcd.length)
    (rawFits : 2 * buffers.trace.length < buffers.raw.length)
    (squareLaw : ModularSquareLaw square backend buffers.modulus buffers.table buffers.trace.length) :
    ∃ attempts length basis lengthOut traceOut gcdOut rawOut,
      let accepted := decide (prefixSlice gcdOut self.degree.val = traceOut)
      let reply := if accepted then .Ok .Gcd else .Err .NotSplit
      Roots.trace square gf64 backend self buffers meter =
        .ok (.Ok reply, { self with attempts, trace_len := lengthOut, checked := accepted },
          { buffers with trace := traceOut, gcd := gcdOut, raw := rawOut, basis := ⟨some basis, length⟩ },
          id, splitMeter) ∧
      attempts.val = self.attempts.val + 1 ∧
      self.direction.val < length.val ∧
      length.val = max (cacheInitialLength buffers) (self.direction.val + 1) ∧
      length.val ≤ 64 ∧ cachePrefix self.splitter_seed basis length.val ∧
      lengthOut.val ≤ traceOut.length ∧ traceOut.length = buffers.trace.length ∧
      gcdOut.length = buffers.gcd.length ∧ rawOut.length = buffers.raw.length ∧
      traceInvariant buffers.modulus (basisWord self.splitter_seed self.direction.val) 64 lengthOut traceOut ∧
      ∃ (before splitDst : Slice U64) (splitInputRaw : Slice RawProduct) (splitLen : Usize),
        before.length = buffers.trace.length ∧ splitDst.length = buffers.gcd.length ∧
        splitInputRaw.length = buffers.raw.length ∧
        traceOut.val = before.val.take lengthOut.val ++ List.replicate (before.length - lengthOut.val) 0#u64 ∧
        square gf64 backend (prefixSlice before lengthOut.val) buffers.modulus buffers.table splitDst splitInputRaw =
          .ok (splitLen, gcdOut, rawOut) := by
  obtain ⟨attempts, attemptNormal, attemptVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := self.attempts) (y := 1#usize) (by exact counterFits))
  obtain ⟨oldLength, oldBasis, getNormal, positive, width, cacheCorrect, oldExact⟩ :=
    cache_ready backend self buffers cached
  obtain ⟨length, basis, extendNormal, lengthVal, finalCorrect, _⟩ :=
    basis_extension_refines self.splitter_seed self.direction oldLength oldBasis directionFits positive width cacheCorrect
  have directionLive : self.direction.val < length.val := by
    rw [lengthVal]
    exact Nat.lt_of_succ_le (Nat.le_max_right _ _)
  have exactBasisLength : length.val = max (cacheInitialLength buffers) (self.direction.val + 1) := by
    rw [lengthVal, oldExact]
  have finalWidth : length.val ≤ 64 := by rw [lengthVal]; exact max_le width (by omega)
  let splitter := basisWord self.splitter_seed self.direction.val
  have read := read_normal basis (UScalar.cast .Usize self.direction)
    (by rw [U32.cast_Usize_val_eq]; exact directionFits)
  rw [U32.cast_Usize_val_eq, finalCorrect _ directionLive] at read
  have startLen := trace_start_length buffers.trace splitter
  have fill := fill_zero buffers.trace
  have zeroLen : (zeroWords buffers.trace).length = buffers.trace.length := by simp [zeroWords, Slice.length]
  have update := Reconstruction.update_normal (zeroWords buffers.trace) 1#usize splitter
    (by change (1#usize).val < (zeroWords buffers.trace).length; rw [zeroLen]
        exact Nat.lt_of_succ_le traceFits)
  let range : core.ops.range.Range U32 := ⟨1#u32, 64#u32⟩
  obtain ⟨out, traceOut, gcdOut, rawOut, loopNormal, outFits, traceLen, gcdLen, rawLen, correct⟩ :=
    trace_loop_refines square backend range 2#usize buffers.modulus (traceStart buffers.trace splitter)
      buffers.gcd buffers.table buffers.raw splitter (by decide) (by decide) (by decide)
      (by rwa [startLen]) (by change 2 ≤ _; rwa [startLen]) (by rwa [startLen]) (by rwa [startLen])
      (by rwa [startLen]) (trace_start_invariant _ _ _ traceFits)
  have traceWidth : traceOut.length = buffers.trace.length := traceLen.trans startLen
  have prefixSize : (prefixSlice traceOut out.val).length ≤ buffers.trace.length := by
    rw [prefix_length, Nat.min_eq_left outFits, ← traceWidth]
    exact outFits
  obtain ⟨splitLen, splitGcd, splitRaw, splitNormal, _, splitGcdLen, splitRawLen, _⟩ :=
    squareLaw (prefixSlice traceOut out.val) gcdOut rawOut prefixSize (by omega) (by omega)
  have cut := shared_prefix_normal traceOut out outFits
  have cmp := shared_prefix_normal splitGcd self.degree (by omega)
  obtain ⟨⟨tail, back⟩, tailNormal, _, tailLength, restore⟩ := RawMulTable.normal_of_spec _ _
    (core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut.step_spec ⟨out⟩ traceOut outFits)
  let padded := back (zeroWords tail)
  have paddedLen : padded.length = traceOut.length := by
    change (back (zeroWords tail)).val.length = traceOut.val.length
    rw [restore, List.length_setSlice!]
  have samePrefix : prefixSlice padded out.val = prefixSlice traceOut out.val := by
    apply Slice.ext
    simp only [padded, prefixSlice, Slice.from_val, restore, List.setSlice!]
    have upper : out.val ≤ traceOut.val.length := outFits
    let front := traceOut.val.take out.val
    have length : front.length = out.val := by rw [show front = _ from rfl, List.length_take, Nat.min_eq_left upper]
    have takeFront (suffix : List U64) : (front ++ suffix).take out.val = front := by
      have taken : (front ++ suffix).take front.length = front := List.take_left
      simpa only [length] using taken
    rw [List.append_assoc]
    exact takeFront _
  have padCorrect : traceInvariant buffers.modulus splitter 64 out padded := by
    intro x root
    rw [samePrefix]
    exact correct x root
  have padValue : padded.val =
      traceOut.val.take out.val ++ List.replicate (traceOut.length - out.val) 0#u64 := by
    change (back (zeroWords tail)).val = _
    rw [restore]
    have endDrop : List.drop (out.val + (traceOut.val.length - out.val)) traceOut.val = [] :=
      List.drop_eq_nil_iff.mpr (by have bound : out.val ≤ traceOut.val.length := outFits; omega)
    have width : traceOut.length = traceOut.val.length := rfl
    simp only [List.setSlice!, zeroWords, Slice.from_val, tailLength, width, List.length_replicate,
      Nat.min_self, List.take_replicate, Nat.min_self, endDrop, List.append_nil]
  have fillTail := fill_zero tail
  have compare := slice_ne (prefixSlice splitGcd self.degree.val) padded
  refine ⟨attempts, length, basis, out, padded, splitGcd, splitRaw, ?_, ?_, directionLive, exactBasisLength, finalWidth, finalCorrect,
    by omega, paddedLen.trans traceWidth, splitGcdLen.trans gcdLen, splitRawLen.trans rawLen, padCorrect,
    traceOut, gcdOut, rawOut, splitLen, traceWidth, gcdLen, rawLen, padValue, splitNormal⟩
  · simp only [Roots.trace, charged, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
    dsimp! only
    simp only [attemptNormal, getNormal, bind_ok]
    dsimp! only
    have bits : gf64.BITS = Result.ok 64#u32 := by
      change Result.ok bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS = _
      rw [bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS]
    simp only [extendNormal, bind_ok]
    dsimp! only
    simp only [lift, read, fill, update, bind_ok, bits,
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS,
      show (1#usize).val = 1 by decide,
      show basisWord self.splitter_seed self.direction.val = splitter from rfl,
      show (zeroWords buffers.trace).setAtNat 1 splitter = traceStart buffers.trace splitter from rfl,
      show ({ start := 1#u32, «end» := 64#u32 } : core.ops.range.Range U32) = range from rfl,
      loopNormal, checked, Bool.false_eq_true, ite_false, splitPaid]
    dsimp! only
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      Slice.index_SliceIndexRangeToUsizeSliceInst, cut, splitNormal]
    dsimp! only
    simp only [Slice.index_mut_SliceIndexRangeFromUsizeSliceInst, tailNormal, bind_ok]
    dsimp! only
    simp only [fillTail, Slice.index_SliceIndexRangeToUsizeSliceInst, cmp, bind_ok, show back (zeroWords tail) = padded from rfl, compare]
    by_cases equal : prefixSlice splitGcd self.degree.val = padded
    · simp [equal]
      rfl
    · simp [equal]
      rfl
  · exact attemptVal


theorem trace_split_checked_refines (square : RootTraceRuntime.ModularSquare) {K : Type}
    (backend : BulkKernels K bulksketch.field.Gf64) (self : Roots) (buffers : FactorWork)
    (meter paidMeter splitMeter : WorkMeter)
    (charged : bulksketch.decode.roots.charge meter (.Trace self.degree) = .ok (.Ok (), paidMeter))
    (splitPaid : bulksketch.decode.roots.charge paidMeter (.SplitCheck self.degree) =
      .ok (.Ok (), splitMeter))
    (degreeFits : self.degree.val ≤ buffers.gcd.length)
    (checked : self.checked = false) (counterFits : self.attempts.val + 1 ≤ Usize.max)
    (directionFits : self.direction.val < 64) (cached : cacheWellFormed self buffers)
    (traceFits : 2 ≤ buffers.trace.length) (gcdFits : buffers.trace.length ≤ buffers.gcd.length)
    (rawFits : 2 * buffers.trace.length < buffers.raw.length)
    (squareLaw : ModularSquareLaw square backend buffers.modulus buffers.table buffers.trace.length) :
    ∃ attempts length basis lengthOut traceOut gcdOut rawOut,
      let accepted := decide (prefixSlice gcdOut self.degree.val = traceOut)
      let reply := if accepted then .Ok .Gcd else .Err .NotSplit
      Roots.trace square gf64 backend self buffers meter =
        .ok (.Ok reply, { self with attempts, trace_len := lengthOut, checked := accepted },
          { buffers with trace := traceOut, gcd := gcdOut, raw := rawOut, basis := ⟨some basis, length⟩ },
          id, splitMeter) ∧
      attempts.val = self.attempts.val + 1 ∧
      self.direction.val < length.val ∧
      length.val = max (cacheInitialLength buffers) (self.direction.val + 1) ∧
      length.val ≤ 64 ∧ cachePrefix self.splitter_seed basis length.val ∧
      lengthOut.val ≤ traceOut.length ∧ traceOut.length = buffers.trace.length ∧
      gcdOut.length = buffers.gcd.length ∧ rawOut.length = buffers.raw.length ∧
      traceInvariant buffers.modulus (basisWord self.splitter_seed self.direction.val) 64 lengthOut traceOut := by
  obtain ⟨attempts, length, basis, size, trace, gcd, raw, ran, attempt, live, cacheLen, cacheBound, cached,
    sizeBound, traceLen, gcdLen, rawLen, invariant, _⟩ :=
    trace_split_checked_evidence square backend self buffers meter paidMeter splitMeter charged splitPaid
      degreeFits checked counterFits directionFits cached traceFits gcdFits rawFits squareLaw
  exact ⟨attempts, length, basis, size, trace, gcd, raw, ran, attempt, live, cacheLen, cacheBound, cached,
    sizeBound, traceLen, gcdLen, rawLen, invariant⟩

private theorem multiply_price (left right : U64) :
    bulksketch.decode.work.mul left right = .ok (WorkSchedule.checkedCost (left.val * right.val)) :=
  WorkSchedule.mul_refines left right

private theorem add_price (left right : U64) :
    bulksketch.decode.work.add left right = .ok (WorkSchedule.checkedCost (left.val + right.val)) :=
  BmPrice.add_refines left right

private theorem squareMod_cost_returns (degree : Usize) :
    ∃ cost, bulksketch.decode.work.square_mod degree = .ok cost := by
  obtain ⟨word, number, _⟩ := WorkSchedule.number_refines degree
  have squareNormal :
      bulksketch.decode.work.square degree = .ok (WorkSchedule.checkedCost (word.val * word.val)) := by
    simp [bulksketch.decode.work.square, number, multiply_price,
      core.result.Result.Insts.CoreOpsTry.branch]
  unfold bulksketch.decode.work.square_mod
  rw [squareNormal]
  cases first : WorkSchedule.checkedCost (word.val * word.val) with
  | Err reason =>
    refine ⟨.Err reason, ?_⟩
    simp [bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
  | Ok value =>
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, multiply_price]
    cases triple : WorkSchedule.checkedCost ((3#u64).val * value.val) with
    | Err reason =>
      refine ⟨.Err reason, ?_⟩
      simp [bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
    | Ok tripleValue =>
      simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, number, multiply_price]
      cases twice : WorkSchedule.checkedCost ((2#u64).val * word.val) with
      | Err reason =>
        refine ⟨.Err reason, ?_⟩
        simp [bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
      | Ok twiceValue =>
        refine ⟨WorkSchedule.checkedCost (tripleValue.val + twiceValue.val), ?_⟩
        simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, add_price]

private theorem trace_cost_returns (degree : Usize) :
    ∃ cost, bulksketch.decode.work.WorkScheduleV1.cost (.Trace degree) = .ok cost := by
  obtain ⟨square, squareNormal⟩ := squareMod_cost_returns degree
  simp only [bulksketch.decode.work.WorkScheduleV1.cost, squareNormal, bind_ok,
    core.result.Result.Insts.CoreOpsTry.branch]
  cases square with
  | Err reason =>
    exact ⟨.Err reason, by simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]⟩
  | Ok value =>
    simp only [bind_ok, add_price]
    cases next : WorkSchedule.checkedCost (value.val + (2#u64).val) with
    | Err reason =>
      exact ⟨.Err reason, by simp [bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]⟩
    | Ok value =>
      simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, multiply_price]
      cases total : WorkSchedule.checkedCost ((63#u64).val * value.val) with
      | Err reason =>
        exact ⟨.Err reason, by simp [bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]⟩
      | Ok cost => exact ⟨.Ok cost, by simp [bind_ok, core.result.Result.Insts.CoreOpsTry.branch]⟩

private theorem split_cost_returns (degree : Usize) :
    ∃ cost, bulksketch.decode.work.WorkScheduleV1.cost (.SplitCheck degree) = .ok cost := by
  obtain ⟨square, squareNormal⟩ := squareMod_cost_returns degree
  obtain ⟨word, number, _⟩ := WorkSchedule.number_refines degree
  simp only [bulksketch.decode.work.WorkScheduleV1.cost, squareNormal, bind_ok,
    core.result.Result.Insts.CoreOpsTry.branch]
  cases square with
  | Err reason =>
    exact ⟨.Err reason, by simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]⟩
  | Ok value =>
    simp only [bind_ok, number, add_price, core.result.Result.Insts.CoreOpsTry.branch]
    cases increment : WorkSchedule.checkedCost (word.val + (1#u64).val) with
    | Err reason =>
      exact ⟨.Err reason, by simp [bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]⟩
    | Ok next =>
      simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, add_price]
      cases total : WorkSchedule.checkedCost (value.val + next.val) with
      | Err reason =>
        exact ⟨.Err reason, by simp [bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]⟩
      | Ok cost => exact ⟨.Ok cost, by simp [bind_ok, core.result.Result.Insts.CoreOpsTry.branch]⟩

theorem trace_wrapper_refines : ActualTraceWrapper := by
  intro square K backend roots buffers meter
  obtain ⟨firstCost, firstPrice⟩ := trace_cost_returns roots.degree
  obtain ⟨first, paidMeter, firstEq⟩ : ∃ first paidMeter, StageCharge.chargeResult meter firstCost = (first, paidMeter) :=
    ⟨_, _, rfl⟩
  have charged :
      bulksketch.decode.roots.charge meter (.Trace roots.degree) = .ok (first, paidMeter) := by
    rw [ClosedLeafAdvance.charge_refines]
    simp only [firstPrice, bind_ok, firstEq]
  refine ⟨first, paidMeter, charged, ?_⟩
  cases first with
  | Err failure => exact trace_charge_failure square backend roots buffers meter paidMeter failure charged
  | Ok paid =>
    cases paid
    intro ready squareLaw
    cases checked : roots.checked with
    | true =>
      obtain ⟨attempts, length, basis, len, trace, gcd, raw, result, correct⟩ :=
        trace_checked_refines square backend roots buffers meter paidMeter charged checked
          ready.counter ready.direction ready.cache ready.trace ready.gcd ready.raw squareLaw
      exact ⟨⟨attempts, length, basis, len, trace, gcd, raw⟩, correct, by simpa only [TraceWrites.frame, checked] using result⟩
    | false =>
      obtain ⟨secondCost, secondPrice⟩ := split_cost_returns roots.degree
      obtain ⟨second, splitMeter, secondEq⟩ : ∃ second splitMeter,
          StageCharge.chargeResult paidMeter secondCost = (second, splitMeter) := ⟨_, _, rfl⟩
      have splitCharged :
          bulksketch.decode.roots.charge paidMeter (.SplitCheck roots.degree) = .ok (second, splitMeter) := by
        rw [ClosedLeafAdvance.charge_refines]
        simp only [secondPrice, bind_ok, secondEq]
      refine ⟨second, splitMeter, splitCharged, ?_⟩
      cases second with
      | Err failure =>
        obtain ⟨attempts, length, basis, len, trace, gcd, raw, result, correct⟩ :=
          trace_split_charge_failure square backend roots buffers meter paidMeter splitMeter failure charged
            splitCharged checked ready.counter ready.direction ready.cache ready.trace ready.gcd ready.raw squareLaw
        exact ⟨⟨attempts, length, basis, len, trace, gcd, raw⟩, correct, by simpa only [TraceWrites.frame, checked] using result⟩
      | Ok paid =>
        cases paid
        obtain ⟨attempts, length, basis, len, trace, gcd, raw, result, correct⟩ :=
          trace_split_checked_refines square backend roots buffers meter paidMeter splitMeter charged
            splitCharged ready.compare checked ready.counter ready.direction ready.cache ready.trace ready.gcd ready.raw squareLaw
        exact ⟨⟨attempts, length, basis, len, trace, gcd, raw⟩, correct, result⟩

end BulksketchBridge.RootTrace
