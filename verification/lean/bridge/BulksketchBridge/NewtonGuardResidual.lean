import BulksketchBridge.NewtonGuardResidualSpec
import BulksketchBridge.Algebra.WordNative
import Mathlib.Tactic.IntervalCases

namespace BulksketchBridge.NewtonGuardResidual

open Aeneas Aeneas.Std Aeneas.Std.WP Algebra.Gf64
open bulksketch.backend.contract bulksketch.decode.deg34
open BulksketchProofs.Field

set_option maxRecDepth 2048

private theorem mul_normal {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : CorrectArithmetic kernels) (left right : U64) :
    kernels.ArithmeticInst.mul left right = .ok (mulWord left right) :=
  (arithmetic.1 left right).trans (native_mul_word left right)

private theorem square_normal {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : CorrectArithmetic kernels) (word : U64) :
    kernels.ArithmeticInst.square word = .ok (squareWord word) :=
  (arithmetic.2 word).trans (Square.square_refines word)

private theorem read_normal (words : Slice U64) (index : Usize) (bounded : index.val < words.length) :
    Slice.index_usize words index = Result.ok words[index.val]! := by
  obtain ⟨word, normal, exactWord⟩ := RawMulTable.normal_of_spec _ _
    (Slice.index_usize_spec words index bounded)
  rw [normal, exactWord, Slice.getElem!_Nat_eq]
  exact congrArg Result.ok (List.Inhabited_getElem_eq_getElem! _ _ bounded)

private theorem iterate_after_square (count : Nat) (word : BitVec 64) :
    Period.iterateSquare count (Period.squareWord word) = Period.iterateSquare (count + 1) word := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [Period.iterateSquare, ih]

private theorem square_loop {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : CorrectArithmetic kernels) (iter : RangeU32) (word : U64) :
    guard_loop0_loop0_loop0 fieldDictionary kernels iter word =
      Result.ok (⟨Period.iterateSquare (iter.«end».val - iter.start.val) word.bv⟩ : U64) := by
  suffices run : ∀ count (range : RangeU32) (observed : U64),
      range.«end».val - range.start.val = count →
      guard_loop0_loop0_loop0 fieldDictionary kernels range observed =
        Result.ok (⟨Period.iterateSquare count observed.bv⟩ : U64) from
    run _ iter word rfl
  intro count
  induction count using Nat.strong_induction_on with
  | h count ih =>
    intro range observed remaining
    by_cases active : range.start.val < range.«end».val
    · obtain ⟨⟨option, next⟩, normal, post⟩ := RawMulTable.normal_of_spec _ _
        (core.iter.range.IteratorRange.next_U32_some_spec range active)
      obtain ⟨rfl, advanced, sameEnd⟩ := post
      have decreased : next.«end».val - next.start.val < count := by
        rw [advanced, sameEnd]
        omega
      have exactCount : next.«end».val - next.start.val + 1 = count := by
        rw [advanced, sameEnd]
        omega
      have step : guard_loop0_loop0_loop0.body fieldDictionary kernels range observed =
          .ok (.cont (next, squareWord observed)) := by
        simp only [guard_loop0_loop0_loop0.body, normal, bind_ok]
        dsimp! only
        simp only [square_normal kernels arithmetic, bind_ok]
      conv => lhs; unfold guard_loop0_loop0_loop0 loop
      dsimp only
      simp only [step, bind_ok]
      change guard_loop0_loop0_loop0 fieldDictionary kernels next (squareWord observed) = _
      rw [ih _ decreased next (squareWord observed) rfl]
      congr 1
      apply U64.bv_eq_imp_eq
      change Period.iterateSquare (next.«end».val - next.start.val) (Period.squareWord observed.bv) =
        Period.iterateSquare count observed.bv
      rw [iterate_after_square, exactCount]
    · obtain ⟨⟨option, next⟩, normal, post⟩ := RawMulTable.normal_of_spec _ _
        (core.iter.range.IteratorRange.next_U32_none_spec range (by omega))
      obtain ⟨noneEq, nextEq⟩ := post
      rw [noneEq, nextEq] at normal
      have finished : count = 0 := by omega
      have step : guard_loop0_loop0_loop0.body fieldDictionary kernels range observed =
          .ok (.done observed) := by
        simp only [guard_loop0_loop0_loop0.body, normal, bind_ok]
        rfl
      conv => lhs; unfold guard_loop0_loop0_loop0 loop
      dsimp only
      simp only [step, bind_ok, finished, Period.iterateSquare]

theorem square_loops_refine : ActualGuardSquareLoops := by
  intro K kernels arithmetic iter word
  exact ⟨square_loop kernels arithmetic iter word, square_loop kernels arithmetic iter word⟩

/-- The odd source index and its repeated squarings represent this exact power. -/
theorem power_decomposition (power : Nat) (positive : 1 ≤ power) (bounded : power < 16) :
    (2 * observationIndex power + 1) * 2 ^ squaresFor power = power := by
  interval_cases power <;> decide

private abbrev nextLag :=
  core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next core.iter.range.StepUsize

private theorem lag_step {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : CorrectArithmetic kernels) (odd out : Slice U64) (degree exponent : Usize)
    (iter next : Inclusive) (accumulator : U64) (bounds : LagBounds iter odd degree out exponent)
    (active : iter.start.val ≤ degree.val) (step : nextLag iter = .ok (some iter.start, next)) :
    guard_loop0_loop0.body fieldDictionary kernels odd degree out exponent iter accumulator =
      .ok (.cont (next, accumulator ^^^ lagTerm odd out degree.val exponent.val iter.start.val)) := by
  have positive := bounds.positive
  have lower := bounds.exponentLower
  have upper := bounds.exponentUpper
  have oddBound := bounds.oddBound
  have outBound := bounds.outBound
  obtain ⟨power, powerNormal, powerVal, _⟩ := RawMulTable.normal_of_spec _ _
    (Usize.sub_spec (x := exponent) (y := iter.start) (by omega))
  obtain ⟨squares, ctzNormal, ctzVal, ctzBound⟩ := usize_trailing_zeros_nibble power (by omega) (by omega)
  change squares.val = squaresFor power.val at ctzVal
  obtain ⟨shifted, shiftNormal, shiftedVal, _⟩ := RawMulTable.normal_of_spec _ _
    (Usize.ShiftRight_spec power squares (by
      rcases System.Platform.numBits_eq with width | width <;> omega))
  obtain ⟨half, halfNormal, halfVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.div_spec shifted (y := 2#usize) (by simp))
  have observation : half.val = observationIndex (exponent.val - iter.start.val) := by
    rw [halfVal, shiftedVal, ctzVal, powerVal]
    rfl
  have shiftLe : shifted.val ≤ power.val := by
    rw [shiftedVal, Nat.shiftRight_eq_div_pow]
    exact Nat.div_le_self _ _
  have observedFits : half.val < odd.length := by
    change half.val = shifted.val / 2 at halfVal
    omega
  obtain ⟨coefficient, coefficientNormal, coefficientVal, _⟩ := RawMulTable.normal_of_spec _ _
    (Usize.sub_spec (x := degree) (y := iter.start) active)
  have observed := read_normal odd half observedFits
  have coefficientRead := read_normal out coefficient (by omega)
  have squareRun := square_loop kernels arithmetic ⟨0#u32, squares⟩ odd[half.val]!
  change guard_loop0_loop0_loop0 fieldDictionary kernels ⟨0#u32, squares⟩ odd[half.val]! =
    .ok (⟨Period.iterateSquare (squares.val - 0) odd[half.val]!.bv⟩ : U64) at squareRun
  simp only [guard_loop0_loop0.body, step, bind_ok]
  dsimp! only
  simp only [powerNormal, ctzNormal, shiftNormal, halfNormal, observed, squareRun, coefficientNormal,
    coefficientRead, mul_normal kernels arithmetic, bind_ok, lift, Nat.sub_zero]
  rw [observation, coefficientVal, ctzVal, powerVal]
  rfl

private theorem lag_next {iter : Inclusive}
    (active : ¬(iter.exhausted = true ∨ iter.«end».val < iter.start.val)) :
    ∃ next : Inclusive, nextLag iter = .ok (some iter.start, next) ∧
      next.«end» = iter.«end» ∧ iter.start.val ≤ next.start.val ∧
      remainingLags next + 1 = remainingLags iter ∧
      (next.start.val = iter.start.val + 1 ∨ remainingLags next = 0) := by
  obtain ⟨⟨option, next⟩, normal, post⟩ := RawMulTable.normal_of_spec _ _
    (core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next_Usize_spec iter)
  simp only [uncurry'_pair, ite_eq_right active] at post
  have openRange : iter.exhausted = false := by cases h : iter.exhausted <;> simp_all
  by_cases advances : iter.start.val < iter.«end».val
  · rw [ite_eq_left advances] at post
    obtain ⟨rfl, startEq, endEq, exhaustedEq⟩ := post
    refine ⟨next, normal, endEq, by omega, ?_, Or.inl startEq⟩
    simp only [remainingLags, exhaustedEq, openRange, Bool.false_eq_true, ite_false, endEq, startEq]
    omega
  · rw [ite_eq_right advances] at post
    obtain ⟨rfl, startEq, endEq, exhaustedEq⟩ := post
    refine ⟨next, normal, endEq, by rw [startEq], ?_, Or.inr ?_⟩
    · simp only [remainingLags, exhaustedEq, openRange, Bool.false_eq_true, ite_true, ite_false]
      omega
    · simp [remainingLags, exhaustedEq]

private theorem lag_loop {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : CorrectArithmetic kernels) (iter : Inclusive) (odd : Slice U64)
    (degree : Usize) (out : Slice U64) (exponent : Usize) (accumulator : U64)
    (bounds : LagBounds iter odd degree out exponent) :
    guard_loop0_loop0 fieldDictionary kernels iter odd degree out exponent accumulator =
      Result.ok (residualFrom odd out degree.val exponent.val iter.start.val accumulator (remainingLags iter)) := by
  suffices run : ∀ count (range : Inclusive) (value : U64),
      remainingLags range = count → LagBounds range odd degree out exponent →
      guard_loop0_loop0 fieldDictionary kernels range odd degree out exponent value =
        Result.ok (residualFrom odd out degree.val exponent.val range.start.val value count) from
    run _ iter accumulator rfl bounds
  intro count
  induction count using Nat.strong_induction_on with
  | h count ih =>
    intro range value remaining admitted
    by_cases stop : range.exhausted = true ∨ range.«end».val < range.start.val
    · obtain ⟨⟨option, next⟩, normal, post⟩ := RawMulTable.normal_of_spec _ _
        (core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next_Usize_spec range)
      simp only [uncurry'_pair, ite_eq_left stop] at post
      obtain ⟨noneEq, nextEq⟩ := post
      rw [noneEq, nextEq] at normal
      have finished : count = 0 := by
        rcases stop with exhausted | past
        · simp [remainingLags, exhausted] at remaining; omega
        · rw [← remaining]
          unfold remainingLags
          split <;> omega
      have step : guard_loop0_loop0.body fieldDictionary kernels odd degree out exponent range value =
          .ok (.done value) := by
        simp only [guard_loop0_loop0.body, normal, bind_ok]
        rfl
      conv => lhs; unfold guard_loop0_loop0 loop
      dsimp only
      simp only [step, bind_ok, finished, residualFrom]
    · have active : range.start.val ≤ degree.val := by
        have endEq := admitted.last
        rw [← endEq]
        omega
      obtain ⟨next, normal, endEq, monotone, countEq, nextShape⟩ := lag_next stop
      let updated := value ^^^ lagTerm odd out degree.val exponent.val range.start.val
      have step := lag_step kernels arithmetic odd out degree exponent range next value admitted active normal
      have nextBounds : LagBounds next odd degree out exponent :=
        { admitted with positive := admitted.positive.trans monotone, last := endEq.trans admitted.last }
      have recursive := ih _ (by omega) next updated rfl nextBounds
      conv => lhs; unfold guard_loop0_loop0 loop
      dsimp only
      simp only [step, bind_ok]
      change guard_loop0_loop0 fieldDictionary kernels next odd degree out exponent updated = _
      rw [recursive, ← remaining, ← countEq, residualFrom]
      rcases nextShape with advance | exhausted
      · rw [advance]
      · rw [exhausted, residualFrom, residualFrom]

theorem lag_loops_refine : ActualGuardLagLoops := by
  intro K kernels arithmetic iter odd degree out exponent accumulator bounds
  exact ⟨lag_loop kernels arithmetic iter odd degree out exponent accumulator bounds,
    lag_loop kernels arithmetic iter odd degree out exponent accumulator bounds⟩

private abbrev nextIndex := core.iter.range.IteratorRange.next core.iter.range.StepUsize

private theorem residual_step {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : CorrectArithmetic kernels) (odd out : Slice U64) (degree : Usize)
    (denominator : U64) (iter next : RangeUsize)
    (step : nextIndex iter = .ok (some iter.start, next))
    (degreeCase : degree.val = 3 ∨ degree.val = 4) (startBound : degree.val ≤ iter.start.val)
    (oddBound : iter.start.val < odd.length) (indexBound : iter.start.val < degree.val + 2)
    (outBound : degree.val ≤ out.length) :
    guard_loop0.body fieldDictionary kernels odd degree out denominator iter =
      .ok (if residualWord odd out denominator degree.val iter.start.val = 0#u64
        then .cont next else .done false) := by
  obtain ⟨twice, twiceNormal, twiceVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.mul_spec (x := 2#usize) (y := iter.start) (by scalar_tac))
  change twice.val = 2 * iter.start.val at twiceVal
  obtain ⟨exponent, exponentNormal, exponentVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := twice) (y := 1#usize) (by scalar_tac))
  change exponent.val = twice.val + 1 at exponentVal
  rw [twiceVal] at exponentVal
  let lags : Inclusive := ⟨1#usize, degree, false⟩
  have lagBounds : LagBounds lags odd degree out exponent :=
    { positive := by change 1 ≤ 1; exact Nat.le_refl _, last := rfl, exponentLower := by omega, exponentUpper := by omega,
      oddBound := by omega, outBound := outBound }
  have run := lag_loop kernels arithmetic lags odd degree out exponent
    (mulWord denominator odd[iter.start.val]!) lagBounds
  have lagCount : remainingLags lags = degree.val := by
    simp [remainingLags, lags]
  change guard_loop0_loop0 fieldDictionary kernels ⟨1#usize, degree, false⟩ odd degree out exponent
    (mulWord denominator odd[iter.start.val]!) = .ok
      (residualFrom odd out degree.val exponent.val 1 (mulWord denominator odd[iter.start.val]!) (remainingLags lags)) at run
  rw [lagCount, exponentVal] at run
  change _ = Result.ok (residualWord odd out denominator degree.val iter.start.val) at run
  simp only [guard_loop0.body, step, bind_ok]
  dsimp! only
  simp only [twiceNormal, exponentNormal, read_normal odd iter.start oddBound, mul_normal kernels arithmetic,
    core.ops.range.RangeInclusive.new, run, bind_ok]
  by_cases zero : residualWord odd out denominator degree.val iter.start.val = 0#u64 <;> simp [zero]

private theorem residual_loop {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : CorrectArithmetic kernels) (iter : RangeUsize) (odd : Slice U64)
    (degree : Usize) (out : Slice U64) (denominator : U64)
    (degreeCase : degree.val = 3 ∨ degree.val = 4) (startBound : degree.val ≤ iter.start.val)
    (endBound : iter.«end».val ≤ min odd.length (degree.val + 2)) (outBound : degree.val ≤ out.length) :
    guard_loop0 fieldDictionary kernels iter odd degree out denominator =
      Result.ok (residualChecks odd out denominator degree.val iter.start.val (iter.«end».val - iter.start.val)) := by
  suffices run : ∀ count (range : RangeUsize),
      range.«end».val - range.start.val = count →
      degree.val ≤ range.start.val → range.«end».val ≤ min odd.length (degree.val + 2) →
      guard_loop0 fieldDictionary kernels range odd degree out denominator =
        Result.ok (residualChecks odd out denominator degree.val range.start.val count) from
    run _ iter rfl startBound endBound
  intro count
  induction count using Nat.strong_induction_on with
  | h count ih =>
    intro range remaining starts ends
    by_cases active : range.start.val < range.«end».val
    · obtain ⟨⟨option, next⟩, normal, post⟩ := RawMulTable.normal_of_spec _ _
        (core.iter.range.IteratorRange.next_Usize_some_spec range active)
      obtain ⟨rfl, advanced, sameEnd⟩ := post
      have degreeEnd : range.«end».val ≤ degree.val + 2 := ends.trans (Nat.min_le_right _ _)
      have oddEnd : range.«end».val ≤ odd.length := ends.trans (Nat.min_le_left _ _)
      have step := residual_step kernels arithmetic odd out degree denominator range next normal
        degreeCase starts (by omega) (by omega) outBound
      have decrease : next.«end».val - next.start.val < count := by rw [advanced, sameEnd]; omega
      have countEq : next.«end».val - next.start.val + 1 = count := by rw [advanced, sameEnd]; omega
      have recursive := ih _ decrease next rfl (by rw [advanced]; omega) (by rwa [sameEnd])
      rw [advanced] at recursive
      conv => lhs; unfold guard_loop0 loop
      rw [step, ← countEq, residualChecks]
      by_cases zero : residualWord odd out denominator degree.val range.start.val = 0#u64
      · simp only [zero, decide_true, Bool.true_and, ite_true, bind_ok]
        change guard_loop0 fieldDictionary kernels next odd degree out denominator = _
        simpa only [advanced] using recursive
      · simp only [zero, decide_false, Bool.false_and, ite_false, bind_ok]
    · obtain ⟨⟨option, next⟩, normal, post⟩ := RawMulTable.normal_of_spec _ _
        (core.iter.range.IteratorRange.next_Usize_none_spec range (by omega))
      obtain ⟨noneEq, nextEq⟩ := post
      rw [noneEq, nextEq] at normal
      have finished : count = 0 := by omega
      have step : guard_loop0.body fieldDictionary kernels odd degree out denominator range =
          .ok (.done true) := by
        simp only [guard_loop0.body, normal, bind_ok]
        rfl
      conv => lhs; unfold guard_loop0 loop
      simp only [step, bind_ok, finished, residualChecks]

theorem guard_loop0_refines {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : CorrectArithmetic kernels) (iter : RangeUsize) (odd : Slice U64)
    (degree : Usize) (out : Slice U64) (denominator : U64)
    (degreeCase : degree.val = 3 ∨ degree.val = 4) (startBound : degree.val ≤ iter.start.val)
    (endBound : iter.«end».val ≤ min odd.length (degree.val + 2)) (outBound : degree.val ≤ out.length) :
    guard_loop0 fieldDictionary kernels iter odd degree out denominator =
      Result.ok (residualChecks odd out denominator degree.val iter.start.val (iter.«end».val - iter.start.val)) :=
  residual_loop kernels arithmetic iter odd degree out denominator degreeCase startBound endBound outBound

theorem guard_loop1_refines {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : CorrectArithmetic kernels) (iter : RangeUsize) (odd : Slice U64)
    (degree : Usize) (out : Slice U64) (denominator : U64)
    (degreeCase : degree.val = 3 ∨ degree.val = 4) (startBound : degree.val ≤ iter.start.val)
    (endBound : iter.«end».val ≤ min odd.length (degree.val + 2)) (outBound : degree.val ≤ out.length) :
    guard_loop1 fieldDictionary kernels iter odd degree out denominator =
      Result.ok (residualChecks odd out denominator degree.val iter.start.val (iter.«end».val - iter.start.val)) :=
  residual_loop kernels arithmetic iter odd degree out denominator degreeCase startBound endBound outBound

theorem residual_loops_refine : ActualGuardResidualLoops := by
  intro K kernels arithmetic iter odd degree out denominator degreeCase startBound endBound outBound
  exact ⟨guard_loop0_refines kernels arithmetic iter odd degree out denominator degreeCase startBound endBound outBound,
    guard_loop1_refines kernels arithmetic iter odd degree out denominator degreeCase startBound endBound outBound⟩

/-- The boolean scan checks exactly the selected residual equations. -/
theorem residualChecks_true_iff (odd out : Slice U64) (denominator : U64) (degree index count : Nat) :
    residualChecks odd out denominator degree index count = true ↔
      ∀ offset, offset < count → residualWord odd out denominator degree (index + offset) = 0#u64 := by
  induction count generalizing index with
  | zero => simp [residualChecks]
  | succ count ih =>
    simp only [residualChecks, Bool.and_eq_true, decide_eq_true_eq, ih]
    constructor
    · rintro ⟨current, rest⟩ offset bounded
      cases offset with
      | zero => simpa using current
      | succ offset => simpa [Nat.add_assoc, Nat.add_comm 1 offset] using rest offset (by omega)
    · intro checked
      refine ⟨by simpa using checked 0 (by omega), ?_⟩
      intro offset bounded
      simpa [Nat.add_assoc, Nat.add_comm 1 offset] using checked (offset + 1) (by omega)

end BulksketchBridge.NewtonGuardResidual
