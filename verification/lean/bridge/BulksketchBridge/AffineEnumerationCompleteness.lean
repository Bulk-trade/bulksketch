import BulksketchBridge.AffineEnumerationFrame
import BulksketchBridge.AffineEnumerationCoset
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Data.List.FinRange

namespace BulksketchBridge.AffineEnumerate

open Aeneas Aeneas.Std DenseCoefficient RebuiltLfsr
open Algebra.Gf64 AffineSubspaceAlgebra AffineSubspaces SliceKernels Polynomial
open bulksketch.backend.contract bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

def accepted : List (U64 × U64) → List U64
  | [] => []
  | (point, value) :: rest =>
    if value = 0#u64 then point :: accepted rest else accepted rest

private theorem take_pushed (roots : Slice U64) (index : Nat) (point : U64)
    (room : index < roots.length) :
    (roots.setAtNat index point).val.take (index + 1) = roots.val.take index ++ [point] := by
  have active : index < (roots.setAtNat index point).val.length := by
    change index < (roots.setAtNat index point).length
    rwa [Slice.setAtNat_length]
  rw [List.take_succ_eq_append_getElem active]
  have read := Slice.getElem_Nat_setAtNat_eq roots index point room
  rw [read]
  simp only [Slice.setAtNat, Slice.from_val, List.take_set_of_le (Nat.le_refl index)]

/-- If all accepted points are nonzero and fit, the exact scan appends them
    in their original order. The result includes the prior written prefix. -/
theorem scan_accepts {degree found : Nat} (pairs : List (U64 × U64)) (roots : Slice U64)
    (room : degree ≤ roots.length) (fits : found + (accepted pairs).length ≤ degree)
    (nonzero : ∀ point ∈ accepted pairs, point ≠ 0#u64) :
    ∃ written,
      scan degree pairs roots found = (none, written, found + (accepted pairs).length) ∧
      written.val.take (found + (accepted pairs).length) = roots.val.take found ++ accepted pairs := by
  induction pairs generalizing roots found with
  | nil =>
    exact ⟨roots, by simp [scan, accepted], by simp [accepted]⟩
  | cons pair rest ih =>
    obtain ⟨point, value⟩ := pair
    by_cases vanishes : value = 0#u64
    · have admitted : accepted ((point, value) :: rest) = point :: accepted rest := by
        simp only [accepted, vanishes, ite_true]
      have pointNZ : point ≠ 0#u64 := nonzero point (by simp [admitted])
      rw [admitted, List.length_cons] at fits
      have active : found < degree := by omega
      have roomAt : found < roots.length := active.trans_le room
      obtain ⟨written, normal, writtenPrefix⟩ := ih (found := found + 1) (roots.setAtNat found point)
        (by simpa only [Slice.setAtNat_length] using room) (by omega)
        (fun later member => nonzero later (by simp [admitted, member]))
      have countEq : found + (point :: accepted rest).length = found + 1 + (accepted rest).length := by
        simp only [List.length_cons]
        omega
      refine ⟨written, ?_, ?_⟩
      · rw [admitted, countEq]
        simpa [scan, vanishes, pointNZ, Nat.ne_of_lt active]
          using normal
      · rw [admitted, countEq, writtenPrefix, take_pushed roots found point roomAt, List.append_assoc]
        rfl
    · have skipped : accepted ((point, value) :: rest) = accepted rest := by
        simp only [accepted, vanishes, ite_false]
      obtain ⟨written, normal, writtenPrefix⟩ := ih (found := found) roots room
        (by simpa only [skipped] using fits) (by simpa only [skipped] using nonzero)
      exact ⟨written, by rw [scan, ite_eq_left vanishes, skipped]; exact normal,
        by simpa only [skipped] using writtenPrefix⟩

private theorem word_zero (word : U64) : toField word.bv = 0 ↔ word = 0#u64 := by
  constructor
  · intro zero
    apply U64.bv_eq_imp_eq
    exact wordFieldEquiv.injective (zero.trans toField_zero.symm)
  · intro zero
    subst word
    exact toField_zero

noncomputable def selectRoots (polynomial : Polynomial Field) (points : List Field) : List Field := by
  classical
  exact points.filter fun point => decide (polynomial.eval point = 0)

private theorem accepted_fields (polynomial : Polynomial Field) (points values : List U64)
    (aligned : points.length = values.length)
    (evaluated : ∀ i < points.length, toField values[i]!.bv = polynomial.eval (toField points[i]!.bv)) :
    (accepted (points.zip values)).map (fun word => toField word.bv) =
      selectRoots polynomial (points.map (fun word => toField word.bv)) := by
  classical
  induction points generalizing values with
  | nil => rfl
  | cons point points ih =>
    cases values with
    | nil => simp at aligned
    | cons value values =>
      have tails : points.length = values.length := by simpa only [List.length_cons, Nat.add_right_cancel_iff] using aligned
      have head : toField value.bv = polynomial.eval (toField point.bv) := by
        simpa only [List.getElem!_cons_zero] using evaluated 0 (by simp)
      have remainder := ih values tails (by
        intro i active
        simpa only [List.getElem!_cons_succ] using evaluated (i + 1) (by simp; omega))
      have zero : polynomial.eval (toField point.bv) = 0 ↔ value = 0#u64 := by rw [← head, word_zero]
      by_cases root : value = 0#u64 <;> simp [selectRoots, accepted, root, zero] <;>
        exact remainder

noncomputable def graySegment (basis : Slice U64) (base : Field) (start count : Nat) : List Field :=
  List.ofFn fun index : Fin count => grayPointValue basis base (start + index.val)

noncomputable def rootsBetween (polynomial : Polynomial Field) (basis : Slice U64)
    (base : Field) (start count : Nat) : List Field :=
  selectRoots polynomial (graySegment basis base start count)

theorem roots_between_split (polynomial : Polynomial Field) (basis : Slice U64) (base : Field)
    (start first second : Nat) :
    rootsBetween polynomial basis base start (first + second) =
      rootsBetween polynomial basis base start first ++ rootsBetween polynomial basis base (start + first) second := by
  classical
  unfold rootsBetween graySegment selectRoots
  rw [List.ofFn_add, List.filter_append]
  simp only [Fin.val_castLE, Fin.val_natAdd, Nat.add_assoc]

private theorem batch_values (polynomial : Slice U64) (basis : Slice U64) (base : Field)
    (points evaluated : Slice U64) (start count : Nat)
    (pointLength : points.length = count) (valueLength : evaluated.length = count)
    (pointsCorrect : ∀ i < count, toField points[i]!.bv = grayPointValue basis base (start + i))
    (valueCorrect : ∀ i < count, toField evaluated[i]!.bv =
      (slicePolynomial polynomial).eval (toField points[i]!.bv)) :
    (accepted (points.val.zip evaluated.val)).map (fun word => toField word.bv) =
      rootsBetween (slicePolynomial polynomial) basis base start count := by
  have listMeaning := accepted_fields (slicePolynomial polynomial) points.val evaluated.val
    (pointLength.trans valueLength.symm) (by
      intro i active
      have inside : i < count := by change i < points.length at active; omega
      simpa only [Slice.getElem!_Nat_eq] using valueCorrect i inside)
  rw [listMeaning]
  congr 1
  apply List.ext_getElem (by simp only [List.length_map, graySegment, List.length_ofFn]; exact pointLength)
  intro i _ rightRoom
  have inside : i < count := by simpa only [graySegment, List.length_ofFn] using rightRoom
  have inWords : i < points.val.length := by change i < points.length; omega
  unfold graySegment at rightRoom ⊢
  rw [List.getElem_map, List.getElem_ofFn, List.Inhabited_getElem_eq_getElem! _ i inWords,
    ← Slice.getElem!_Nat_eq, pointsCorrect i inside]

private theorem selected_zero (polynomial : Polynomial Field) (basis : Slice U64) (base point : Field)
    (start count : Nat) (member : point ∈ rootsBetween polynomial basis base start count) :
    polynomial.eval point = 0 := by
  classical
  simp only [rootsBetween, selectRoots, List.mem_filter, decide_eq_true_eq] at member
  exact member.2

/-- Complete batch composition when the factor has no zero root and the
    qualifying Gray points fit. It collects exactly the roots in Gray order
    and uses the original terminal degree check. -/
theorem batches_collect {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (horner : HornerLaw kernels) (rejoin : Slice U64 × Slice U64 → Slice U64)
    (polynomial basis : Slice U64) (base : Field) (degree batch stop start : Nat)
    (roots points values : Slice U64) (point : U64) (found : Nat)
    (positive : 0 < batch) (pointRoom : batch ≤ points.length) (valueRoom : batch ≤ values.length)
    (rootRoom : degree ≤ roots.length) (within : stop ≤ 2 ^ basis.length) (fits : stop ≤ Usize.max)
    (zeroFree : (slicePolynomial polynomial).eval 0 ≠ 0)
    (preceding : toField point.bv = grayPointValue basis base (start - 1))
    (countRoom : found + (rootsBetween (slicePolynomial polynomial) basis base start (stop - start)).length ≤ degree) :
    let expected := rootsBetween (slicePolynomial polynomial) basis base start (stop - start)
    let total := found + expected.length
    ∃ written scratch,
      enumerateBatches kernels rejoin polynomial basis degree batch stop start roots points values point found =
        .ok (if total = degree then .Ok (ClosedLeafAdvance.usizeWord degree) else .Err .NotSplit, written, scratch) ∧
      (written.val.take total).map (fun word => toField word.bv) =
        (roots.val.take found).map (fun word => toField word.bv) ++ expected := by
  dsimp only
  suffices ∀ fuel start found (roots points values : Slice U64) (point : U64),
      stop - start = fuel → batch ≤ points.length → batch ≤ values.length → degree ≤ roots.length →
      toField point.bv = grayPointValue basis base (start - 1) →
      found + (rootsBetween (slicePolynomial polynomial) basis base start (stop - start)).length ≤ degree →
      let expected := rootsBetween (slicePolynomial polynomial) basis base start (stop - start)
      let total := found + expected.length
      ∃ written scratch,
        enumerateBatches kernels rejoin polynomial basis degree batch stop start roots points values point found =
          .ok (if total = degree then .Ok (ClosedLeafAdvance.usizeWord degree) else .Err .NotSplit, written, scratch) ∧
        (written.val.take total).map (fun word => toField word.bv) =
          (roots.val.take found).map (fun word => toField word.bv) ++ expected
    from this _ start found roots points values point rfl pointRoom valueRoom rootRoom preceding countRoom
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro start found roots points values point remaining pointRoom valueRoom rootRoom prior enough
    dsimp only
    by_cases active : start < stop
    · let width := min batch (stop - start)
      let left := prefixSlice points width
      let right := prefixSlice values width
      have widthPositive : 0 < width := Nat.lt_min.mpr ⟨positive, by omega⟩
      have pointWidth : left.length = width := by
        rw [show left = prefixSlice points width from rfl, prefix_length, Nat.min_eq_left (by omega)]
      have valueWidth : right.length = width := by
        rw [show right = prefixSlice values width from rfl, prefix_length, Nat.min_eq_left (by omega)]
      let filled := grayFill basis start left 0 point width
      have filledWidth : filled.2.length = width :=
        (gray_fill_words basis left start 0 point width (by omega)).2.1.trans pointWidth
      obtain ⟨nextPoint, pointMeaning⟩ :=
        gray_fill_field_points basis left base start 0 width point (by omega) (by omega) (by omega)
          (by simpa only [Nat.add_zero] using prior)
      obtain ⟨evaluated, evalNormal, evalWidth, valuesMeaning⟩ :=
        horner polynomial filled.2 right (filledWidth.trans valueWidth.symm)
      let pairs := List.zip filled.2.val evaluated.val
      let acceptedWords := accepted pairs
      let p := slicePolynomial polynomial
      let selected := rootsBetween p basis base start width
      let rest := rootsBetween p basis base (start + width) (stop - (start + width))
      have selectedWords : acceptedWords.map (fun word => toField word.bv) = selected :=
        batch_values polynomial basis base filled.2 evaluated start width filledWidth (evalWidth.trans valueWidth)
          (fun i inside => pointMeaning i (Nat.zero_le _) (by simpa only [Nat.zero_add] using inside))
          (fun i inside => valuesMeaning i (by rwa [filledWidth]))
      have selectedCount : acceptedWords.length = selected.length := by
        have lengths := congrArg List.length selectedWords
        rwa [List.length_map] at lengths
      have collectAll : rootsBetween p basis base start (stop - start) = selected ++ rest := by
        have range : stop - start = width + (stop - (start + width)) := by omega
        conv_lhs => rw [range]
        exact roots_between_split p basis base start width (stop - (start + width))
      change found + (rootsBetween p basis base start (stop - start)).length ≤ degree at enough
      rw [collectAll, List.length_append] at enough
      have nonzero : ∀ word ∈ acceptedWords, word ≠ 0#u64 := by
        intro word present isZero
        have valueMember : toField word.bv ∈ selected := by
          rw [← selectedWords]
          exact List.mem_map.mpr ⟨word, present, rfl⟩
        have vanishes := selected_zero p basis base _ start width valueMember
        rw [(word_zero word).mpr isZero] at vanishes
        exact zeroFree vanishes
      obtain ⟨written, scanNormal, writtenPrefix⟩ :=
        scan_accepts pairs roots rootRoom (by change found + acceptedWords.length ≤ degree; omega) nonzero
      have frame := (scan_frame degree pairs roots found (by omega)).1
      rw [scanNormal] at frame
      let nextPoints := restorePrefix points filled.2
      let nextValues := restorePrefix values evaluated
      have nextPrior : toField filled.1.bv = grayPointValue basis base (start + width - 1) := by
        simpa only [Nat.add_zero] using nextPoint
      obtain ⟨output, scratch, nextNormal, nextWords⟩ :=
        ih _ (by omega) (start + width) (found + acceptedWords.length) written nextPoints nextValues
          filled.1 rfl (by simpa only [nextPoints, restore_length] using pointRoom)
          (by simpa only [nextValues, restore_length] using valueRoom) (by simpa only using frame.symm ▸ rootRoom)
          nextPrior (by change found + acceptedWords.length + rest.length ≤ degree; omega)
      have totalEq : found + (rootsBetween p basis base start (stop - start)).length =
          (found + acceptedWords.length) + rest.length := by
        rw [collectAll, List.length_append, selectedCount, Nat.add_assoc]
      refine ⟨output, scratch, ?_, ?_⟩
      · change _ = Result.ok ((if found + (rootsBetween p basis base start (stop - start)).length = degree then
          .Ok (ClosedLeafAdvance.usizeWord degree) else .Err .NotSplit : core.result.Result Usize DecodeFailure),
          output, scratch)
        rw [totalEq, enumerateBatches, dite_eq_left ⟨active, positive⟩]
        change (do
          let evaluated ← kernels.horner_many polynomial filled.2 right
          let (failure, nextRoots, nextCount) := scan degree (filled.2.val.zip evaluated.val) roots found
          match failure with
          | some reason => .ok (core.result.Result.Err reason, nextRoots, rejoin (nextPoints, restorePrefix values evaluated))
          | none =>
            enumerateBatches kernels rejoin polynomial basis degree batch stop (start + width)
              nextRoots nextPoints (restorePrefix values evaluated) filled.1 nextCount) = _
        simp only [evalNormal, Bind.bind, bind_ok, scanNormal, pairs]
        simpa only [acceptedWords, rest, p, nextValues] using nextNormal
      · change (output.val.take (found + (rootsBetween p basis base start (stop - start)).length)).map _ =
          (roots.val.take found).map _ ++ rootsBetween p basis base start (stop - start)
        rw [totalEq, nextWords, collectAll]
        simp only [writtenPrefix, List.map_append, selectedWords, List.append_assoc, acceptedWords, rest, p]
    · have empty : stop - start = 0 := by omega
      have selected : rootsBetween (slicePolynomial polynomial) basis base start (stop - start) = [] := by
        simp [empty, rootsBetween, graySegment, selectRoots]
      refine ⟨roots, rejoin (points, values), ?_, ?_⟩
      · rw [enumerateBatches, dite_eq_right (fun guard => active guard.1), selected]
        by_cases exactCount : found = degree <;> simp [exactCount]
      · simp only [selected, List.length_nil, Nat.add_zero, List.append_nil]

theorem gray_roots_membership (polynomial : Polynomial Field) (basis : Slice U64) (base point : Field) :
    point ∈ rootsBetween polynomial basis base 0 (2 ^ basis.length) ↔
      polynomial.IsRoot point ∧ point ∈ coset base (prefixDirections basis basis.length) := by
  classical
  simp only [rootsBetween, selectRoots, List.mem_filter, decide_eq_true_eq, IsRoot, graySegment,
    List.mem_ofFn, Nat.zero_add, and_comm]
  rw [gray_coset_membership]
  constructor
  · rintro ⟨isRoot, ⟨index, exactPoint⟩⟩
    exact ⟨isRoot, index.val, index.isLt, exactPoint⟩
  · rintro ⟨isRoot, index, bound, exactPoint⟩
    exact ⟨isRoot, ⟨⟨index, bound⟩, exactPoint⟩⟩

theorem gray_roots_distinct (polynomial : Polynomial Field) (basis : Slice U64) (base : Field)
    (independent : IndependentDirections basis) :
    (rootsBetween polynomial basis base 0 (2 ^ basis.length)).Nodup := by
  classical
  unfold rootsBetween selectRoots
  apply List.Nodup.filter
  unfold graySegment
  apply List.nodup_ofFn_ofInjective
  intro left right same
  apply Fin.ext
  simp only [Nat.zero_add] at same
  exact gray_points_distinct basis base independent left.isLt right.isLt same

private theorem represented_degree (polynomial : Slice U64) (positive : 0 < polynomial.length)
    (leading : polynomial[polynomial.length - 1]! = 1#u64) :
    (slicePolynomial polynomial).natDegree = polynomial.length - 1 ∧ slicePolynomial polynomial ≠ 0 := by
  have top : (slicePolynomial polynomial).coeff (polynomial.length - 1) = 1 := by
    have one : toField (1#u64).bv = 1 := toField_one
    rw [slicePolynomial_coeff, ite_eq_left (by omega), leading, one]
  have nonzero : (slicePolynomial polynomial).coeff (polynomial.length - 1) ≠ 0 :=
    top.symm ▸ one_ne_zero
  refine ⟨Nat.le_antisymm ?_ (le_natDegree_of_ne_zero nonzero), ?_⟩
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i greater
    rw [slicePolynomial_coeff, ite_eq_right (by omega)]
  · intro zero
    rw [zero, coeff_zero] at nonzero
    exact nonzero rfl

open BmEntry in
/-- For a split factor with distinct, nonzero roots in the affine coset,
    the original enumerator returns its entire root set exactly once. -/
def ActualNativeEnumerationComplete : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    HornerLaw kernels → ∀ (polynomial : Slice U64) (base : U64) (basis roots work : Slice U64),
    0 < polynomial.length → polynomial.length - 1 ≤ roots.length →
    2 ≤ work.length → basis.length < System.Platform.numBits →
    polynomial[polynomial.length - 1]! = 1#u64 →
    (slicePolynomial polynomial).eval 0 ≠ 0 →
    (slicePolynomial polynomial).Splits → (slicePolynomial polynomial).roots.Nodup →
    IndependentDirections basis →
    (∀ point, (slicePolynomial polynomial).IsRoot point →
      point ∈ coset (toField base.bv) (prefixDirections basis basis.length)) →
    let degree := polynomial.length - 1
    ∃ written scratch,
      bulksketch.decode.affine.enumerate fieldDictionary kernels polynomial base basis roots work =
        .ok (.Ok (ClosedLeafAdvance.usizeWord degree), written, scratch) ∧
      written.length = roots.length ∧ scratch.length = work.length ∧
      let candidates := (written.val.take degree).map (fun word => toField word.bv)
      candidates.Nodup ∧ ∀ point, point ∈ candidates ↔ (slicePolynomial polynomial).IsRoot point

open BmEntry in
theorem native_enumeration_complete : ActualNativeEnumerationComplete := by
  intro K kernels horner polynomial base basis roots work polyPositive rootRoom workRoom rank
    leading zeroFree splits simple independent contains
  classical
  dsimp only
  let degree := polynomial.length - 1
  let p := slicePolynomial polynomial
  let count := 2 ^ basis.length
  let listed := rootsBetween p basis (toField base.bv) 0 count
  have distinct : listed.Nodup := gray_roots_distinct p basis _ independent
  obtain ⟨natDegree, nonzero⟩ := represented_degree polynomial polyPositive leading
  have rootSet : listed.toFinset = p.roots.toFinset := by
    ext point
    rw [List.mem_toFinset, Multiset.mem_toFinset, mem_roots nonzero]
    change point ∈ rootsBetween p basis (toField base.bv) 0 count ↔ p.IsRoot point
    rw [gray_roots_membership]
    exact ⟨And.left, fun root => ⟨root, contains point root⟩⟩
  have listedCount : listed.length = degree := by
    rw [← List.toFinset_card_of_nodup distinct, rootSet, Multiset.toFinset_card_of_nodup simple,
      ← splits.natDegree_eq_card_roots]
    exact natDegree
  let half := work.length / 2
  have halfPositive : 0 < half := by unfold half; omega
  have batchBounds : 0 < batchWidth half ∧ batchWidth half ≤ half := by
    unfold batchWidth
    split <;> omega
  have countFits : count ≤ Usize.max := by
    have small : 2 ^ basis.length < 2 ^ System.Platform.numBits :=
      Nat.pow_lt_pow_right (by decide) rank
    simp only [count, Usize.max, Usize.numBits, UScalarTy.numBits]
    omega
  obtain ⟨written, scratch, modeled, represented⟩ :=
    batches_collect kernels horner (splitBack work half) polynomial basis (toField base.bv)
      degree (batchWidth half) count 0 roots (prefixSlice work half) (tail work half) base 0
      batchBounds.1
      (by rw [prefix_length, Nat.min_eq_left (by unfold half; omega)]; exact batchBounds.2)
      (by rw [tail_length]; unfold half at *; omega)
      rootRoom (by rfl) countFits zeroFree (by simpa using (gray_point_zero basis (toField base.bv)).symm)
      (by simpa only [Nat.sub_zero, Nat.zero_add, listed, count, p, degree] using listedCount.le)
  have exactRun :
      bulksketch.decode.affine.enumerate fieldDictionary kernels polynomial base basis roots work =
        .ok (.Ok (ClosedLeafAdvance.usizeWord degree), written, scratch) := by
    exact (native_enumerate_refines kernels horner polynomial base basis roots work
      polyPositive rootRoom workRoom rank).trans (by simpa only [Nat.sub_zero, Nat.zero_add, listedCount,
        eq_self, ite_true, half, count, p, degree, listed] using modeled)
  obtain ⟨reply, rootFrame, workFrame, ran, rootLen, workLen, _⟩ :=
    native_enumeration_frame kernels horner polynomial base basis roots work polyPositive rootRoom workRoom rank
  have frameEq := Result.ok_injective (ran.symm.trans exactRun)
  have rootEq := congrArg (fun frame : BatchResult => frame.2.1) frameEq
  have workEq := congrArg (fun frame : BatchResult => frame.2.2) frameEq
  change rootFrame = written at rootEq
  change workFrame = scratch at workEq
  have listedWords : (written.val.take degree).map (fun word => toField word.bv) = listed := by
    simpa only [Nat.sub_zero, Nat.zero_add, List.take_zero, List.map_nil, List.nil_append,
      listedCount, listed, count, p, degree] using represented
  refine ⟨written, scratch, exactRun, rootEq ▸ rootLen, workEq ▸ workLen, ?_⟩
  rw [← show degree = polynomial.length - 1 from rfl, listedWords]
  refine ⟨distinct, ?_⟩
  intro point
  rw [show listed = rootsBetween p basis (toField base.bv) 0 (2 ^ basis.length) from rfl, gray_roots_membership]
  exact ⟨And.left, fun root => ⟨root, contains point root⟩⟩

end BulksketchBridge.AffineEnumerate
