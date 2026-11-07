import BulksketchBridge.OddRecurrenceSpec
import BulksketchBridge.Algebra.WordNative
import BulksketchBridge.RawMulTable

/-! The actual nested loops compute the continuation through their original
ranges, raw product XOR and early return. Arithmetic callbacks have explicit
GF64 contracts and slice reads are proved in bounds. -/
namespace BulksketchBridge.OddRecurrence

open Aeneas Aeneas.Std Aeneas.Std.WP
open BulksketchBridge.Algebra.Gf64 BulksketchProofs.Field
open bulksketch.backend.contract
open scoped BigOperators

private abbrev Raw := bulksketch.types.RawProduct
private abbrev Inclusive := core.ops.range.RangeInclusive Usize
private abbrev Range := core.ops.range.Range Usize

private noncomputable def rawValue (product : Raw) : Field :=
  toField (reduceFold64 product.lo.bv product.hi.bv)

private theorem rawValue_xor (left right : Raw) :
    rawValue { lo := left.lo ^^^ right.lo, hi := left.hi ^^^ right.hi } =
      rawValue left + rawValue right := by
  change toField (reduceFold64 (left.lo.bv ^^^ right.lo.bv) (left.hi.bv ^^^ right.hi.bv)) = _
  rw [reduceFold64_xor, toField_xor]
  rfl

private theorem rawValue_product (left right : U64) :
    rawValue (RawMul.expectedProduct left right) = toField left.bv * toField right.bv :=
  toField_mul left.bv right.bv

private theorem rawValue_zero : rawValue { lo := 0#u64, hi := 0#u64 } = 0 := by
  change toField (reduceFold64 0 0) = 0
  simp [reduceFold64, fold64, overflow64]
  exact toField_zero

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

private theorem inner_loop {Backend : Type} (kernels : BulkKernels Backend bulksketch.field.Gf64)
    (arithmetic : CorrectArithmetic kernels) (odd locator : Slice U64) (index : Usize)
    (inOdd : index.val < odd.length) (range : Inclusive) (accumulator : Raw)
    (starts : 1 ≤ range.start.val) (lagBound : range.«end».val ≤ index.val)
    (inLocator : range.«end».val < locator.length) :
    ∃ output : Raw,
      BulkKernels.odd_recurrence_matches.default_loop0_loop0 kernels range odd locator index accumulator =
        Result.ok output ∧
      rawValue output = rawValue accumulator + lagSum odd locator index.val range.start.val (lagCount range) := by
  suffices ∀ count (range : Inclusive) (accumulator : Raw),
      lagCount range = count → 1 ≤ range.start.val → range.«end».val ≤ index.val →
      range.«end».val < locator.length →
      ∃ output : Raw,
        BulkKernels.odd_recurrence_matches.default_loop0_loop0 kernels range odd locator index accumulator =
          Result.ok output ∧
        rawValue output = rawValue accumulator + lagSum odd locator index.val range.start.val (lagCount range) from
    this (lagCount range) range accumulator rfl starts lagBound inLocator
  intro count
  induction count using Nat.strong_induction_on with
  | h count inductionHypothesis =>
    intro range accumulator countEq starts lagBound inLocator
    by_cases stop : range.exhausted = true ∨ range.«end».val < range.start.val
    · obtain ⟨next, zero⟩ := inclusive_done range stop
      refine ⟨accumulator, ?_, ?_⟩
      · unfold BulkKernels.odd_recurrence_matches.default_loop0_loop0 loop
        dsimp only
        simp only [BulkKernels.odd_recurrence_matches.default_loop0_loop0.body, next, bind_ok]
        dsimp! only
        simp only [bind_ok]
      · simp [lagSum, zero]
    · have active : range.start.val ≤ range.«end».val := by omega
      obtain ⟨next, nextNormal, endEq, startMono, consumed, nextStart⟩ := inclusive_step range stop
      obtain ⟨rowIndex, subtractNormal, subPost⟩ := RawMulTable.normal_of_spec _ _
        (Usize.sub_spec (x := index) (y := range.start) (by omega))
      have rowIndexEq : rowIndex.val = index.val - range.start.val := subPost.1
      have rowRead := read_normal odd rowIndex (by omega)
      have coeffRead := read_normal locator range.start (by omega)
      let product := RawMul.expectedProduct odd[rowIndex.val]! locator[range.start.val]!
      have productNormal : bulksketch.field.gf64.raw_mul fieldDictionary
          odd[rowIndex.val]! locator[range.start.val]! = Result.ok product :=
        RawMul.raw_mul_refines _ _
      let sum : Raw := { lo := accumulator.lo ^^^ product.lo, hi := accumulator.hi ^^^ product.hi }
      have bodyNormal : BulkKernels.odd_recurrence_matches.default_loop0_loop0.body
          kernels odd locator index range accumulator = Result.ok (ControlFlow.cont (next, sum)) := by
        simp only [BulkKernels.odd_recurrence_matches.default_loop0_loop0.body, nextNormal, bind_ok]
        dsimp! only
        simp only [subtractNormal, rowRead, coeffRead, arithmetic.1, bind_ok, lift]
        rw [productNormal]
        simp only [bind_ok, sum]
      obtain ⟨output, normal, meaning⟩ := inductionHypothesis (lagCount next) (by omega) next sum rfl
        (by omega) (by rw [endEq]; exact lagBound) (by rw [endEq]; exact inLocator)
      refine ⟨output, ?_, ?_⟩
      · unfold BulkKernels.odd_recurrence_matches.default_loop0_loop0 loop
        dsimp only
        rw [bodyNormal]
        simpa only [BulkKernels.odd_recurrence_matches.default_loop0_loop0, bind_ok] using normal
      · rw [meaning, sum_step odd locator index.val range next consumed nextStart]
        dsimp only [sum, product]
        rw [rawValue_xor, rawValue_product, rowIndexEq, ← add_assoc]
        rfl

private def rangeAt (odd : Slice U64) (start : Usize) : Range :=
  { start := start, «end» := Slice.len odd }

private theorem outer_loop {Backend : Type} (kernels : BulkKernels Backend bulksketch.field.Gf64)
    (arithmetic : CorrectArithmetic kernels) (odd locator : Slice U64)
    (degree start : Usize) (degreeEq : degree.val = locator.length - 1)
    (nonempty : 0 < locator.length) (lower : degree.val ≤ start.val) :
    ∃ output : Bool,
      BulkKernels.odd_recurrence_matches.default_loop0 kernels (rangeAt odd start) odd locator degree =
        Result.ok output ∧
      (output = true ↔ ∀ index, start.val ≤ index → index < odd.length →
        toField odd[index]!.bv = lagSum odd locator index 1 degree.val) := by
  suffices ∀ count (start : Usize), odd.length - start.val = count → degree.val ≤ start.val →
      ∃ output : Bool,
        BulkKernels.odd_recurrence_matches.default_loop0 kernels (rangeAt odd start) odd locator degree =
          Result.ok output ∧
        (output = true ↔ ∀ index, start.val ≤ index → index < odd.length →
          toField odd[index]!.bv = lagSum odd locator index 1 degree.val) from
    this (odd.length - start.val) start rfl lower
  intro count
  induction count using Nat.strong_induction_on with
  | h count inductionHypothesis =>
    intro start countEq lower
    by_cases active : start.val < odd.length
    · obtain ⟨⟨option, advanced⟩, nextNormal, nextPost⟩ := RawMulTable.normal_of_spec _ _
        (core.iter.range.IteratorRange.next_Usize_some_spec (rangeAt odd start) (by
          simpa [rangeAt] using active))
      obtain ⟨rfl, advancedStart, advancedEnd⟩ := nextPost
      have advanceValue : advanced.start.val = start.val + 1 := advancedStart
      have advanceShape : advanced = rangeAt odd advanced.start := by
        cases advanced
        simp_all [rangeAt]
      rw [advanceShape] at nextNormal
      let lags : Inclusive := { start := 1#usize, «end» := degree, exhausted := false }
      have newRange : core.ops.range.RangeInclusive.new 1#usize degree = Result.ok lags := rfl
      have defaultZero : bulksketch.types.RawProduct.Insts.CoreDefaultDefault.default =
          Result.ok { lo := 0#u64, hi := 0#u64 } := rfl
      obtain ⟨sum, innerNormal, sumValue⟩ := inner_loop kernels arithmetic odd locator start active
        lags { lo := 0#u64, hi := 0#u64 } (by simp [lags]) lower (by
          change degree.val < locator.length
          omega)
      have lagLength : lagCount lags = degree.val := by simp [lagCount, lags]
      obtain ⟨reduced, reduceNormal, reductionBits, _⟩ := Gf64Reduce.reduce_refines sum
      have reducedValue : toField reduced.bv = lagSum odd locator start.val 1 degree.val := by
        rw [reductionBits]
        change rawValue sum = _
        simpa only [lagLength, lags, UScalar.ofNatCore_val_eq, rawValue_zero, zero_add] using sumValue
      have equalAt : reduced = odd[start.val]! ↔
          toField odd[start.val]!.bv = lagSum odd locator start.val 1 degree.val := by
        rw [← reducedValue]
        constructor
        · intro equal
          rw [equal]
        · intro equal
          apply U64.bv_eq_imp_eq
          exact toField_injective equal.symm
      have rowRead := read_normal odd start active
      have bodyNormal : BulkKernels.odd_recurrence_matches.default_loop0.body
          kernels odd locator degree (rangeAt odd start) = Result.ok
            (if reduced = odd[start.val]! then ControlFlow.cont (rangeAt odd advanced.start)
              else ControlFlow.done false) := by
        simp only [BulkKernels.odd_recurrence_matches.default_loop0.body, nextNormal, bind_ok]
        change (do
          let initial ← bulksketch.types.RawProduct.Insts.CoreDefaultDefault.default
          let lags ← core.ops.range.RangeInclusive.new 1#usize degree
          let sum ← BulkKernels.odd_recurrence_matches.default_loop0_loop0 kernels lags odd locator start initial
          let value ← kernels.ArithmeticInst.reduce sum
          let observed ← Slice.index_usize odd start
          if value != observed then Result.ok (ControlFlow.done false)
          else Result.ok (ControlFlow.cont (rangeAt odd advanced.start))) = _
        have exactReduce := (arithmetic.2 sum).trans reduceNormal
        simp only [Bind.bind, defaultZero, newRange, bind_ok, innerNormal, exactReduce, rowRead]
        by_cases equal : reduced = odd[start.val]! <;>
          simp only [bne_iff_ne, ne_eq, equal, not_true_eq_false, not_false_eq_true, ite_true, ite_false]
      by_cases equal : reduced = odd[start.val]!
      · obtain ⟨output, normal, exactTail⟩ := inductionHypothesis (odd.length - advanced.start.val)
          (by omega) advanced.start rfl (by omega)
        refine ⟨output, ?_, ?_⟩
        · unfold BulkKernels.odd_recurrence_matches.default_loop0 loop
          rw [bodyNormal, ite_eq_left equal]
          simpa only [BulkKernels.odd_recurrence_matches.default_loop0, bind_ok] using normal
        · rw [exactTail]
          constructor
          · intro tail index atOrAfter inside
            by_cases same : index = start.val
            · rw [same]
              exact equalAt.mp equal
            · exact tail index (by omega) inside
          · intro all index atOrAfter inside
            exact all index (by omega) inside
      · refine ⟨false, ?_, ?_⟩
        · unfold BulkKernels.odd_recurrence_matches.default_loop0 loop
          rw [bodyNormal, ite_eq_right equal]
          simp only [bind_ok]
        · constructor
          · intro impossible
            contradiction
          · intro all
            exact (equal (equalAt.mpr (all start.val (Nat.le_refl _) active))).elim
    · obtain ⟨⟨option, unchanged⟩, nextNormal, nextPost⟩ := RawMulTable.normal_of_spec _ _
        (core.iter.range.IteratorRange.next_Usize_none_spec (rangeAt odd start) (by
          have stopped : odd.length ≤ start.val := by omega
          simpa [rangeAt] using stopped))
      rw [nextPost.1] at nextNormal
      refine ⟨true, ?_, ?_⟩
      · unfold BulkKernels.odd_recurrence_matches.default_loop0 loop
        simp only [BulkKernels.odd_recurrence_matches.default_loop0.body, nextNormal, bind_ok]
        dsimp! only
        simp only [bind_ok]
      · constructor
        · intro _ index atOrAfter inside
          omega
        · intro _
          rfl

/-- The original scalar default accepts exactly the complete continuation
under the stated GF64 arithmetic callbacks and nonempty locator precondition. -/
theorem default_refines : ActualDefaultMatchesEveryContinuation := by
  intro Backend kernels odd locator arithmetic nonempty
  have fits : (1#usize).val ≤ (Slice.len locator).val := by
    rw [Slice.len_val]
    change 1 ≤ locator.length
    omega
  obtain ⟨degree, subtractNormal, subPost⟩ := RawMulTable.normal_of_spec _ _
    (Usize.sub_spec (x := Slice.len locator) (y := 1#usize) fits)
  have degreeEq : degree.val = locator.length - 1 := by simpa using subPost.1
  obtain ⟨output, normal, meaning⟩ := outer_loop kernels arithmetic odd locator degree degree
    degreeEq nonempty (Nat.le_refl _)
  refine ⟨output, ?_, ?_⟩
  · unfold BulkKernels.odd_recurrence_matches.default
    simp only [subtractNormal, bind_ok]
    exact normal
  · simpa only [degreeEq, continuationMatches] using meaning

end BulksketchBridge.OddRecurrence
