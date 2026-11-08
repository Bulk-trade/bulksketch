import BulksketchBridge.BmDiscrepancySpec
import BulksketchBridge.OddRecurrence
import BulksketchBridge.Gf64Reduce
import BulksketchBridge.RawMul
import Mathlib.Algebra.BigOperators.Fin

namespace BulksketchBridge.BmDiscrepancy

open Aeneas Aeneas.Std Aeneas.Std.WP Algebra.Gf64
open bulksketch.backend.contract bulksketch.decode.bm
open BulksketchProofs.Field
open scoped BigOperators

private abbrev doubleEnded :=
  bulksketch.core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT U64

private abbrev nextZip :=
  core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
    (core.iter.traits.iterator.IteratorSliceIter U64) (BmLocatorRuntime.reverseIterator doubleEnded)

private theorem forward_some (coefficients : Slice U64) (index : Nat) (inBounds : index < coefficients.length) :
    core.slice.iter.IteratorSliceIter.next ⟨coefficients, index⟩ =
      Result.ok (some coefficients.val[index]!, ⟨coefficients, index + 1⟩) := by
  have active : index < coefficients.len := by rw [Slice.len_val]; exact inBounds
  rw [core.slice.iter.IteratorSliceIter.next, dite_eq_left active]
  dsimp! only
  apply congrArg (fun word => Result.ok (some word, (⟨coefficients, index + 1⟩ : Forward)))
  change coefficients[index]'inBounds = _
  rw [Slice.Inhabited_getElem_eq_getElem! coefficients index inBounds, Slice.getElem!_Nat_eq]

private theorem forward_none (coefficients : Slice U64) (index : Nat) (past : coefficients.length ≤ index) :
    core.slice.iter.IteratorSliceIter.next ⟨coefficients, index⟩ =
      Result.ok (none, ⟨coefficients, index⟩) := by
  have inactive : ¬index < coefficients.len := by rw [Slice.len_val]; omega
  rw [core.slice.iter.IteratorSliceIter.next, dite_eq_right inactive]

private theorem reverse_some (syndromes : Slice U64) (word : U64) (rest : List U64)
    (reversed : syndromes.val.reverse = word :: rest) :
    ∃ tail : Slice U64, tail.val.reverse = rest ∧
      core.slice.iter.IteratorSliceIter.next_back ⟨syndromes, 0⟩ = .ok (some word, ⟨tail, 0⟩) := by
  have active : 0 < syndromes.val.length := by
    have size := congrArg List.length reversed
    simp only [List.length_reverse, List.length_cons] at size
    omega
  obtain ⟨⟨item, next⟩, normal, itemEq, nextVals, nextCursor⟩ :=
    RawMulTable.normal_of_spec _ _ (core.slice.iter.IteratorSliceIter.next_back.spec
      (⟨syndromes, 0⟩ : Forward) active)
  have itemExact : item = some word := by
    change item = syndromes.val.getLast? at itemEq
    rw [itemEq, List.getLast?_eq_head?_reverse, reversed]
    rfl
  have nextExact : next = ⟨next.slice, 0⟩ := by cases next; simp_all
  have nextReversed : next.slice.val.reverse = rest := by
    change next.slice.val = syndromes.val.take (syndromes.val.length - 1) at nextVals
    rw [nextVals, ← List.dropLast_eq_take]
    have original : syndromes.val = rest.reverse ++ [word] := by
      simpa using congrArg List.reverse reversed
    rw [original]
    simp
  refine ⟨next.slice, nextReversed, ?_⟩
  rw [normal, itemExact, nextExact]

private theorem reverse_none (syndromes : Slice U64) (empty : syndromes.val.reverse = []) :
    core.slice.iter.IteratorSliceIter.next_back ⟨syndromes, 0⟩ = .ok (none, ⟨syndromes, 0⟩) := by
  have valEmpty : syndromes.val = [] := List.reverse_eq_nil_iff.mp empty
  have inactive : ¬0 < syndromes.val.length := by simp [valEmpty]
  rw [core.slice.iter.IteratorSliceIter.next_back, dite_eq_right inactive]

private theorem reverse_step (syndromes tail : Slice U64) (word : Option U64)
    (step : core.slice.iter.IteratorSliceIter.next_back ⟨syndromes, 0⟩ = .ok (word, ⟨tail, 0⟩)) :
    (BmLocatorRuntime.reverseIterator doubleEnded).next ⟨⟨syndromes, 0⟩⟩ = .ok (word, ⟨⟨tail, 0⟩⟩) := by
  change (do
    let (item, next) ← core.slice.iter.IteratorSliceIter.next_back (⟨syndromes, 0⟩ : Forward)
    Result.ok (item, (⟨next⟩ : Reverse))) = _
  simp only [step, Bind.bind, bind_ok]

private theorem zip_left_done (coefficients syndromes : Slice U64) (index : Nat)
    (past : coefficients.length ≤ index) :
    nextZip (zipAt coefficients syndromes index) = .ok (none, zipAt coefficients syndromes index) := by
  simp only [nextZip, core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
    zipAt, forward_none coefficients index past, bind_ok]
  rfl

private theorem zip_right_done (coefficients syndromes : Slice U64) (index : Nat)
    (inBounds : index < coefficients.length) (empty : syndromes.val.reverse = []) :
    nextZip (zipAt coefficients syndromes index) = .ok (none, zipAt coefficients syndromes (index + 1)) := by
  simp only [nextZip, core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
    zipAt, forward_some coefficients index inBounds, bind_ok]
  dsimp! only
  simp only [reverse_step syndromes syndromes none (reverse_none syndromes empty), bind_ok]
  rfl

private theorem zip_active (coefficients syndromes tail : Slice U64) (index : Nat) (word : U64)
    (inBounds : index < coefficients.length)
    (reverseStep : core.slice.iter.IteratorSliceIter.next_back ⟨syndromes, 0⟩ = .ok (some word, ⟨tail, 0⟩)) :
    nextZip (zipAt coefficients syndromes index) =
      .ok (some (coefficients.val[index]!, word), zipAt coefficients tail (index + 1)) := by
  simp only [nextZip, core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
    zipAt, forward_some coefficients index inBounds, bind_ok]
  dsimp! only
  simp only [reverse_step syndromes tail (some word) reverseStep, bind_ok]
  rfl

private theorem loop_stopped {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (iter stopped : DiscrepancyZip) (initial : Raw) (done : nextZip iter = .ok (none, stopped)) :
    locator_loop0_loop1 fieldDictionary kernels iter initial.lo initial.hi =
      .ok (initial.lo, initial.hi) := by
  unfold locator_loop0_loop1 loop
  dsimp only
  simp only [locator_loop0_loop1.body, done, bind_ok]
  dsimp! only
  simp only [bind_ok]

private theorem loop_advanced {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : RawArithmetic kernels) (iter next : DiscrepancyZip) (initial : Raw)
    (coefficient syndrome : U64) (step : nextZip iter = .ok (some (coefficient, syndrome), next)) :
    let updated := rawXor initial (RawMul.expectedProduct coefficient syndrome)
    locator_loop0_loop1 fieldDictionary kernels iter initial.lo initial.hi =
      locator_loop0_loop1 fieldDictionary kernels next updated.lo updated.hi := by
  have rawNormal := (arithmetic coefficient syndrome).trans (RawMul.raw_mul_refines coefficient syndrome)
  have body : locator_loop0_loop1.body fieldDictionary kernels iter initial.lo initial.hi =
      .ok (.cont (next, (rawXor initial (RawMul.expectedProduct coefficient syndrome)).lo,
        (rawXor initial (RawMul.expectedProduct coefficient syndrome)).hi)) := by
    simp only [locator_loop0_loop1.body, step, bind_ok]
    dsimp! only
    simp only [rawNormal, bind_ok, lift, rawXor]
  dsimp only
  conv => lhs; unfold locator_loop0_loop1 loop
  dsimp only
  simp only [body, bind_ok]
  rfl

private theorem raw_loop {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : RawArithmetic kernels) (coefficients syndromes : Slice U64) (index : Nat) (initial : Raw) :
    let result := rawFold (remainingPairs coefficients syndromes index) initial
    locator_loop0_loop1 fieldDictionary kernels (zipAt coefficients syndromes index) initial.lo initial.hi =
      .ok (result.lo, result.hi) := by
  suffices run : ∀ (remaining : List U64) (window : Slice U64) (cursor : Nat) (product : Raw),
      window.val.reverse = remaining →
      let result := rawFold ((coefficients.val.drop cursor).zip remaining) product
      locator_loop0_loop1 fieldDictionary kernels (zipAt coefficients window cursor) product.lo product.hi =
        .ok (result.lo, result.hi) from run _ syndromes index initial rfl
  intro remaining
  induction remaining with
  | nil =>
    intro window cursor product reversed
    by_cases active : cursor < coefficients.length
    · have done := loop_stopped kernels _ _ product (zip_right_done coefficients window cursor active reversed)
      simpa only [List.zip_nil_right, rawFold, List.foldl_nil] using done
    · have done := loop_stopped kernels _ _ product (zip_left_done coefficients window cursor (by omega))
      simpa only [List.zip_nil_right, rawFold, List.foldl_nil] using done
  | cons word remaining ih =>
    intro window cursor product reversed
    by_cases active : cursor < coefficients.length
    · obtain ⟨tail, tailReversed, reverseStep⟩ := reverse_some window word remaining reversed
      have zipped := zip_active coefficients window tail cursor word active reverseStep
      have advanced := loop_advanced kernels arithmetic _ _ product _ _ zipped
      dsimp only at advanced ⊢
      rw [advanced]
      have forwardDrop : coefficients.val.drop cursor = coefficients.val[cursor]! :: coefficients.val.drop (cursor + 1) := by
        rw [List.drop_eq_getElem_cons active, List.Inhabited_getElem_eq_getElem! _ _ active]
      rw [forwardDrop]
      simp only [rawFold, List.zip_cons_cons, List.foldl_cons]
      exact ih tail (cursor + 1) (rawXor product (RawMul.expectedProduct coefficients.val[cursor]! word)) tailReversed
    · have done := loop_stopped kernels _ _ product (zip_left_done coefficients window cursor (by omega))
      have drop : coefficients.val.drop cursor = [] := List.drop_eq_nil_iff.mpr (by change coefficients.length ≤ cursor; omega)
      simpa only [drop, List.zip_nil_left, rawFold, List.foldl_nil] using done

theorem raw_refines : ActualBmRawDiscrepancy := by
  intro K kernels arithmetic coefficients syndromes index initial
  exact ⟨raw_loop kernels arithmetic coefficients syndromes index initial,
    raw_loop kernels arithmetic coefficients syndromes index initial⟩

private theorem rawValue_xor (left right : Raw) :
    rawValue (rawXor left right) = rawValue left + rawValue right := by
  change toField (reduceFold64 (left.lo.bv ^^^ right.lo.bv) (left.hi.bv ^^^ right.hi.bv)) = _
  rw [reduceFold64_xor, toField_xor]
  rfl

private theorem rawValue_product (left right : U64) :
    rawValue (RawMul.expectedProduct left right) = toField left.bv * toField right.bv :=
  toField_mul left.bv right.bv

theorem raw_dot_product (pairs : List (U64 × U64)) (accumulator : Raw) :
    rawValue (rawFold pairs accumulator) =
      rawValue accumulator + (pairs.map fun pair => toField pair.1.bv * toField pair.2.bv).sum := by
  induction pairs generalizing accumulator with
  | nil => simp [rawFold]
  | cons pair pairs ih =>
    simp only [rawFold, List.foldl_cons]
    change rawValue (rawFold pairs (rawXor accumulator (RawMul.expectedProduct pair.1 pair.2))) = _
    rw [ih, rawValue_xor, rawValue_product]
    simp [add_assoc]

private theorem source_terms (connection syndromes : Slice U64) (degree step : Nat)
    (connectionBound : degree < connection.length) (startBound : degree ≤ step + 1)
    (syndromeBound : step + 1 < syndromes.length) :
    let state := sourceZip connection syndromes degree step
    ((remainingPairs state.fst.slice state.snd.iter.slice 0).map
      fun pair => toField pair.1.bv * toField pair.2.bv).sum =
      ∑ i ∈ Finset.range (degree + 1), toField connection[i]!.bv * toField syndromes[step + 1 - i]!.bv := by
  let left := DenseCoefficient.prefixSlice connection (degree + 1)
  let right := ClosedLeaf.region syndromes (step + 1 - degree) (step + 2)
  let pairs := left.val.zip right.val.reverse
  let term (index : Nat) := toField connection[index]!.bv * toField syndromes[step + 1 - index]!.bv
  have leftVal : left.val = connection.val.take (degree + 1) := by
    simp only [left, DenseCoefficient.prefixSlice, Slice.from_val]
  have leftLen : left.val.length = degree + 1 := by
    rw [leftVal, List.length_take, Nat.min_eq_left (by exact connectionBound)]
  have rightLen : right.val.length = degree + 1 := by
    change right.length = degree + 1
    change (ClosedLeaf.region syndromes (step + 1 - degree) (step + 2)).length = _
    rw [ClosedLeaf.region_length _ _ _ (by omega)]
    omega
  have pairsLen : pairs.length = degree + 1 := by
    simp only [pairs, List.length_zip, List.length_reverse, leftLen, rightLen, Nat.min_self]
  have equal : (pairs.map fun pair => toField pair.1.bv * toField pair.2.bv) =
      List.ofFn (fun index : Fin (degree + 1) => term index.val) := by
    apply List.ext_getElem (by simp [pairsLen])
    intro index bounded mappedBound
    rw [List.getElem_map, List.getElem_ofFn]
    have pairBound : index < pairs.length := by simpa only [List.length_map] using bounded
    have inWindow : index < degree + 1 := by omega
    have leftExact : left.val[index]'(by omega) = connection[index]! := by
      rw [List.getElem_of_eq leftVal, List.getElem_take, Slice.getElem!_Nat_eq,
        List.Inhabited_getElem_eq_getElem!]
      change index < connection.length
      omega
    have rightExact : right.val.reverse[index]'(by rw [List.length_reverse]; omega) =
        syndromes[step + 1 - index]! := by
      rw [List.getElem_reverse]
      have rightVal : right.val =
          (syndromes.val.drop (step + 1 - degree)).take (step + 2 - (step + 1 - degree)) := by
        simp only [right, ClosedLeaf.region, Slice.from_val, List.slice]
      rw [List.getElem_of_eq rightVal, List.getElem_take, List.getElem_drop,
        List.Inhabited_getElem_eq_getElem!, Slice.getElem!_Nat_eq]
      have exactIndex : step + 1 - degree + (right.val.length - 1 - index) = step + 1 - index := by omega
      rw [exactIndex]
      change _ < syndromes.length
      omega
    have pairExact : pairs[index]'pairBound = (connection[index]!, syndromes[step + 1 - index]!) := by
      change (left.val.zip right.val.reverse)[index]'pairBound = _
      rw [List.getElem_zip, leftExact, rightExact]
    rw [pairExact]
  change (pairs.map fun pair => toField pair.1.bv * toField pair.2.bv).sum =
    ∑ i ∈ Finset.range (degree + 1), term i
  rw [equal, List.sum_ofFn, Fin.sum_univ_eq_sum_range]

private theorem raw_zero : rawValue ⟨0#u64, 0#u64⟩ = 0 := by
  change toField (reduceFold64 0 0) = 0
  rw [show reduceFold64 0 0 = 0 by decide]
  exact toField_zero

theorem source_dot_refines : ActualBmSourceDiscrepancy := by
  intro K kernels arithmetic reduction connection syndromes degree step
    connectionBound startBound syndromeBound
  let state := sourceZip connection syndromes degree step
  let initial : Raw := ⟨0#u64, 0#u64⟩
  let product := rawFold (remainingPairs state.fst.slice state.snd.iter.slice 0) initial
  obtain ⟨left, right⟩ := raw_refines kernels arithmetic state.fst.slice state.snd.iter.slice 0 initial
  change locator_loop0_loop1 fieldDictionary kernels state 0#u64 0#u64 =
    .ok (product.lo, product.hi) at left
  change locator_loop0_loop6 fieldDictionary kernels state 0#u64 0#u64 =
    .ok (product.lo, product.hi) at right
  obtain ⟨delta, normal, bits, _⟩ := Gf64Reduce.reduce_refines product
  have reduceNormal : kernels.ArithmeticInst.reduce product = .ok delta := (reduction product).trans normal
  refine ⟨delta, ?_, ?_, ?_⟩
  · change (do
      let pair ← locator_loop0_loop1 fieldDictionary kernels state 0#u64 0#u64
      kernels.ArithmeticInst.reduce ⟨pair.1, pair.2⟩) = Result.ok delta
    simp only [left, bind_ok]
    exact reduceNormal
  · change (do
      let pair ← locator_loop0_loop6 fieldDictionary kernels state 0#u64 0#u64
      kernels.ArithmeticInst.reduce ⟨pair.1, pair.2⟩) = Result.ok delta
    simp only [right, bind_ok]
    exact reduceNormal
  · rw [bits]
    change rawValue product = _
    simp only [product, raw_dot_product, show rawValue initial = 0 from raw_zero, zero_add]
    exact source_terms connection syndromes degree step connectionBound startBound syndromeBound

end BulksketchBridge.BmDiscrepancy
