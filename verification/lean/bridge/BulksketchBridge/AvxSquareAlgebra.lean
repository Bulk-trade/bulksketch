import BulksketchBridge.AvxSquare
import BulksketchBridge.DenseReducerSquareAlgebra
import BulksketchBridge.X86Allocation

namespace BulksketchBridge.AvxSquare

open Aeneas.Std Aeneas.Std.Avx512Register
open Algebra.Gf64 Polynomial DenseReducerAlgebra SliceKernels
open BulksketchProofs.Field Avx512RegisterChallenges
open scoped BigOperators BulksketchBridge.DenseMulReductionSpec

set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

private theorem set_word {T : Type} [Inhabited T] (words : Slice T) (index slot : Nat)
    (value : T) (inside : slot < words.length) :
    (words.setAtNat index value)[slot]! = if index = slot then value else words[slot]! := by
  by_cases same : index = slot
  · subst slot
    rw [Slice.getElem!_Nat_eq, Slice.getElem!_Nat_setAtNat_eq _ _ _ inside, ite_eq_left rfl]
  · rw [Slice.getElem!_Nat_eq, Slice.getElem!_Nat_setAtNat_ne _ _ _ _ same, ← Slice.getElem!_Nat_eq,
      ite_eq_right same]

private theorem scratch_seed_word (input dst : Slice U64) (raw : Slice Raw)
    (start count first slot : Nat) (inside : slot < raw.length) :
    (seed input start first dst raw count).2[slot]! =
      if start ≤ slot ∧ slot < start + count then { raw[slot]! with lo := Square.expectedWord input[slot]! }
      else raw[slot]! := by
  induction count generalizing start dst raw with
  | zero => simp [seed]
  | succ count ih =>
    rw [seed, ih _ _ _ (by simpa only [seed_step_scratch_length])]
    have word : (seedStep input[start]! start first dst raw).2[slot]! =
        if start = slot then { raw[start]! with lo := Square.expectedWord input[start]! } else raw[slot]! := by
      exact set_word raw start slot _ inside
    rw [word]
    by_cases same : start = slot
    · subst slot
      simp only [show ¬(start + 1 ≤ start ∧ start < start + 1 + count) by omega, ite_false,
        show start ≤ start ∧ start < start + (count + 1) by omega, and_self, ite_true]
    · have selected : (start + 1 ≤ slot ∧ slot < start + 1 + count) ↔
          (start ≤ slot ∧ slot < start + (count + 1)) := by omega
      simp only [ite_eq_right same, selected]

private theorem dst_seed_word (input dst : Slice U64) (raw : Slice Raw)
    (start count first slot : Nat) (inside : slot < dst.length) :
    (seed input start first dst raw count).1[slot]! =
      if slot % 2 = 0 ∧ start ≤ slot / 2 ∧ slot / 2 < start + count ∧ slot / 2 < first
      then Square.expectedWord input[slot / 2]! else dst[slot]! := by
  induction count generalizing start dst raw with
  | zero => simp only [seed, Nat.add_zero]; rw [ite_eq_right (by omega)]
  | succ count ih =>
    rw [seed, ih _ _ _ (by simpa only [seed_step_dst_length])]
    have step : (seedStep input[start]! start first dst raw).1[slot]! =
        if 2 * start = slot ∧ start < first then Square.expectedWord input[start]! else dst[slot]! := by
      by_cases low : start < first
      · rw [seedStep, ite_eq_left low, set_word dst (2 * start) slot _ inside]
        simp only [low, and_true]
      · simp only [seedStep, low, ite_false, and_false]
    rw [step]
    by_cases same : 2 * start = slot ∧ start < first
    · have skipLater : ¬(slot % 2 = 0 ∧ start + 1 ≤ slot / 2 ∧ slot / 2 < start + 1 + count ∧ slot / 2 < first) := by omega
      have active : slot % 2 = 0 ∧ start ≤ slot / 2 ∧ slot / 2 < start + (count + 1) ∧ slot / 2 < first := by omega
      rw [ite_eq_right skipLater, ite_eq_left same, ite_eq_left active, show slot / 2 = start by omega]
    · have selected : (slot % 2 = 0 ∧ start + 1 ≤ slot / 2 ∧ slot / 2 < start + 1 + count ∧ slot / 2 < first) ↔
          (slot % 2 = 0 ∧ start ≤ slot / 2 ∧ slot / 2 < start + (count + 1) ∧ slot / 2 < first) := by omega
      simp only [ite_eq_right same, selected]

private theorem region_word (table : Slice U64) (start stop slot : Nat)
    (fit : stop ≤ table.length) (active : start + slot < stop) :
    (ClosedLeaf.region table start stop)[slot]! = table[start + slot]! := by
  simp only [ClosedLeaf.region, Slice.getElem!_Nat_eq, Slice.from_val]
  exact List.getElem!_slice start stop slot table.val ⟨fit, active⟩

private theorem row_load (table : Slice U64) (degree first index offset stop : Nat)
    (pair : Fin 4) (half : Bool) (inside : offset + (X86MaskedMemory.flatIndex pair half).val < stop)
    (stopRoom : stop ≤ degree) (rowBound : (index - first + 1) * degree ≤ table.length) :
    loadWords (rowRegion table degree first index offset stop) pair half =
      (tableRow table degree (index - first))[offset + (X86MaskedMemory.flatIndex pair half).val]!.bv := by
  let start := (index - first) * degree
  let slot := (X86MaskedMemory.flatIndex pair half).val
  have exactEnd : (index - first + 1) * degree = start + degree := by simp [start, Nat.add_mul]
  have fit : start + stop ≤ table.length := by omega
  have firstRead := region_word table (start + offset) (start + stop) slot fit (by omega)
  have fullRead := region_word table start ((index - first + 1) * degree) (offset + slot) rowBound (by omega)
  have length := ClosedLeaf.region_length table (start + offset) (start + stop) fit
  have active : slot < (ClosedLeaf.region table (start + offset) (start + stop)).length := by omega
  unfold loadWords
  rw [ite_eq_left (show slot < (rowRegion table degree first index offset stop).length from active)]
  change (ClosedLeaf.region table (start + offset) (start + stop))[slot]!.bv =
    (ClosedLeaf.region table start ((index - first + 1) * degree))[offset + slot]!.bv
  rw [firstRead, fullRead, Nat.add_assoc]

private theorem reduced_row_step (square : U64) (table : Slice U64) (degree first index offset stop : Nat)
    (even odd : Word512) (pair : Fin 4) (half : Bool) :
    let updated := rowStep square table degree first index offset stop even odd
    reduceRegisters updated.1 updated.2 pair half =
      reduceRegisters even odd pair half ^^^
        multiplyWord square.bv (loadWords (rowRegion table degree first index offset stop) pair half) := by
  cases half <;> simp [rowStep, reduceRegisters, xorRegister, products, multiplyWord, reduceFold64_xor]

noncomputable def scratchTerm (scratch : Slice Raw) (table : Slice U64) (degree first index slot : Nat) : Field :=
  toField scratch[index]!.lo.bv * toField (tableRow table degree (index - first))[slot]!.bv

theorem scanned_rows_field (scratch : Slice Raw) (table : Slice U64)
    (degree first index offset stop count : Nat) (even odd : Word512) (pair : Fin 4) (half : Bool)
    (firstVal : first = firstHigh degree) (high : first ≤ index) (inputBound : scratch.length ≤ degree)
    (remaining : index + count ≤ scratch.length) (stopRoom : stop ≤ degree)
    (inside : offset + (X86MaskedMemory.flatIndex pair half).val < stop)
    (tableBound : degree / 2 * degree ≤ table.length) :
    let sums := scanRows scratch table degree first index offset stop even odd count
    toField (reduceRegisters sums.1 sums.2 pair half) =
      toField (reduceRegisters even odd pair half) +
        ∑ i ∈ Finset.range count, scratchTerm scratch table degree first (index + i)
          (offset + (X86MaskedMemory.flatIndex pair half).val) := by
  induction count generalizing index even odd with
  | zero => simp [scanRows]
  | succ count ih =>
    have rowBound : (index - first + 1) * degree ≤ table.length :=
      (Nat.mul_le_mul_right degree (by unfold firstHigh at firstVal; omega :
        index - first + 1 ≤ degree / 2)).trans tableBound
    let updated := rowStep scratch[index]!.lo table degree first index offset stop even odd
    let slot := offset + (X86MaskedMemory.flatIndex pair half).val
    have shiftSum :
        (∑ i ∈ Finset.range count, scratchTerm scratch table degree first (index + 1 + i) slot) =
        ∑ i ∈ Finset.range count, scratchTerm scratch table degree first (index + (i + 1)) slot := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Nat.add_assoc, Nat.add_comm 1 i]
    change toField (reduceRegisters
      (scanRows scratch table degree first (index + 1) offset stop updated.1 updated.2 count).1
      (scanRows scratch table degree first (index + 1) offset stop updated.1 updated.2 count).2 pair half) = _
    rw [ih (index + 1) updated.1 updated.2 (by omega) (by omega)]
    rw [show reduceRegisters updated.1 updated.2 pair half = _ from
      reduced_row_step scratch[index]!.lo table degree first index offset stop even odd pair half,
      row_load table degree first index offset stop pair half inside stopRoom rowBound, toField_xor, toField_mul]
    change (_ + scratchTerm scratch table degree first index slot) + _ = _
    rw [shiftSum, Finset.sum_range_succ']
    simp only [Nat.add_zero]
    ac_rfl

private theorem store_words_length (words : Slice U64) (value : Word512) (bound : words.length ≤ 8) :
    (storeWords words value bound).length = words.length := by
  simp [storeWords, X86MaskedMemory.registerPayload, Slice.length]

private theorem store_word (words : Slice U64) (value : Word512) (bound : words.length ≤ 8)
    (slot : Nat) (active : slot < words.length) :
    (storeWords words value bound)[slot]!.bv = X86MaskedMemory.flatten value ⟨slot, by omega⟩ := by
  have length : (storeWords words value bound).length = words.length := store_words_length _ _ _
  rw [← Slice.Inhabited_getElem_eq_getElem! _ _ (by omega : slot < (storeWords words value bound).length)]
  rw [Slice.getElem_Nat_eq]
  simp only [storeWords, X86MaskedMemory.registerPayload, Slice.from_val, List.getElem_map, List.getElem_ofFn]
  change slot < (storeWords words value bound).length
  omega


private theorem block_frame (scratch : Slice Raw) (table : Slice U64) (degree first offset stop : Nat)
    (dst : Slice U64) (slot : Nat) (endBound : stop ≤ dst.length)
    (ordered : offset ≤ stop) (outside : slot < offset ∨ stop ≤ slot) :
    (blockStep scratch table degree first offset stop dst)[slot]! = dst[slot]! := by
  let out := ClosedLeaf.region dst offset stop
  have outLen : out.length = stop - offset := ClosedLeaf.region_length _ _ _ endBound
  unfold blockStep
  dsimp only
  split
  · rename_i fits
    rw [Slice.getElem!_Nat_eq, Slice.setSlice!_val, List.getElem!_setSlice!_same,
      ← Slice.getElem!_Nat_eq]
    simp only [storeWords, Slice.from_val, X86MaskedMemory.registerPayload, List.length_map, List.length_ofFn]
    change slot < offset ∨ offset + out.length ≤ slot
    omega
  · rfl

noncomputable def highValue (scratch : Slice Raw) (table : Slice U64) (degree first slot : Nat) : Field :=
  ∑ i ∈ Finset.range (scratch.length - first), scratchTerm scratch table degree first (first + i) slot

private theorem block_slot_field (scratch : Slice Raw) (table : Slice U64) (degree first offset stop : Nat)
    (dst : Slice U64) (slot : Nat) (dstLength : dst.length = degree)
    (inputBound : scratch.length ≤ degree) (firstVal : first = firstHigh degree)
    (endBound : stop ≤ degree) (limited : stop - offset ≤ 8)
    (slotBound : offset ≤ slot ∧ slot < stop)
    (tableBound : degree / 2 * degree ≤ table.length) :
    toField (blockStep scratch table degree first offset stop dst)[slot]!.bv =
      toField dst[slot]!.bv + highValue scratch table degree first slot := by
  let zero : Word512 := fun _ _ => 0
  let accum := scanRows scratch table degree first first offset stop zero zero (scratch.length - first)
  let out := ClosedLeaf.region dst offset stop
  have outLen : out.length = stop - offset := ClosedLeaf.region_length _ _ _ (by omega)
  have fits : out.length ≤ 8 := by omega
  have localSlot : slot - offset < out.length := by omega
  let lane : Fin 8 := ⟨slot - offset, by omega⟩
  let pair : Fin 4 := ⟨lane.val / 2, by omega⟩
  let half := decide (lane.val % 2 = 1)
  have laneIndex : X86MaskedMemory.flatIndex pair half = lane := by
    apply Fin.ext
    simp only [X86MaskedMemory.flatIndex, pair, half, decide_eq_true_eq, lane]
    split <;> omega
  let stored := storeWords out (xorRegister (loadWords out) (reduceRegisters accum.1 accum.2)) fits
  have storeLength : stored.length = out.length := store_words_length _ _ _
  have setWord : (dst.setSlice! offset stored.val)[slot]! = stored[slot - offset]! := by
    simp only [Slice.getElem!_Nat_eq, Slice.setSlice!_val]
    apply List.getElem!_setSlice!_middle
    change offset ≤ slot ∧ slot - offset < stored.length ∧ slot < dst.length
    omega
  have laneWord : stored[slot - offset]!.bv =
      loadWords out pair half ^^^ reduceRegisters accum.1 accum.2 pair half := by
    rw [store_word _ _ fits _ localSlot, ← show lane = ⟨slot - offset, by omega⟩ from rfl,
      ← laneIndex, X86MaskedMemory.flatten_at]
    rfl
  have readWord : loadWords out pair half = dst[slot]!.bv := by
    unfold loadWords
    rw [laneIndex, ite_eq_left localSlot]
    have payload := region_word dst offset stop (slot - offset) (by omega) (by omega)
    change out[slot - offset]!.bv = dst[slot]!.bv
    rw [show out[slot - offset]! = _ from payload, show offset + (slot - offset) = slot by omega]
  have reducedValue : toField (reduceRegisters accum.1 accum.2 pair half) =
      highValue scratch table degree first slot := by
    by_cases hasHigh : first ≤ scratch.length
    · have value := scanned_rows_field scratch table degree first first offset stop (scratch.length - first)
        zero zero pair half firstVal (by omega) inputBound (by omega) endBound
        (by rw [laneIndex]; change offset + (slot - offset) < stop; omega) tableBound
      have zeroValue : toField (reduceRegisters zero zero pair half) = 0 := by
        cases half <;> simp [reduceRegisters, zero, reduceFold64, fold64, overflow64] <;> exact toField_zero
      rw [zeroValue, zero_add, laneIndex, show offset + lane.val = slot by change offset + (slot - offset) = slot; omega]
        at value
      exact value
    · have empty : scratch.length - first = 0 := by omega
      cases half <;> simp [accum, highValue, empty, scanRows, reduceRegisters, zero,
        reduceFold64, fold64, overflow64] <;> exact toField_zero
  have stepExact : blockStep scratch table degree first offset stop dst = dst.setSlice! offset stored.val := by
    unfold blockStep
    dsimp only
    rw [dite_eq_left (show (ClosedLeaf.region dst offset stop).length ≤ 8 from fits)]
  rw [stepExact, setWord, laneWord, toField_xor, readWord, reducedValue]

theorem scanned_blocks_field (scratch : Slice Raw) (table : Slice U64)
    (degree first offset : Nat) (dst : Slice U64) (fuel slot : Nat)
    (dstLength : dst.length = degree) (inputBound : scratch.length ≤ degree)
    (firstVal : first = firstHigh degree) (tableBound : degree / 2 * degree ≤ table.length)
    (inside : slot < degree) (enough : degree - offset ≤ fuel) :
    toField (scanBlocks scratch table degree first offset dst fuel)[slot]!.bv =
      toField dst[slot]!.bv + if offset ≤ slot then highValue scratch table degree first slot else 0 := by
  induction fuel generalizing offset dst with
  | zero =>
    simp only [scanBlocks, ite_eq_right (by omega : ¬ offset ≤ slot), add_zero]
  | succ fuel ih =>
    by_cases active : offset < degree
    · let stop := min (offset + 8) degree
      let dst' := blockStep scratch table degree first offset stop dst
      simp only [scanBlocks, active, ite_true]
      have len : dst'.length = degree := by simp [dst', dstLength]
      have enough' : degree - stop ≤ fuel := by dsimp [stop]; omega
      rw [ih stop dst' len enough']
      have stopBound : stop ≤ degree := by dsimp [stop]; omega
      have ordered : offset ≤ stop := by dsimp [stop]; omega
      by_cases written : offset ≤ slot ∧ slot < stop
      · rw [ite_eq_left written.1, ite_eq_right (by omega : ¬ stop ≤ slot), add_zero]
        exact block_slot_field scratch table degree first offset stop dst slot dstLength inputBound firstVal
          stopBound (by dsimp [stop]; omega) written tableBound
      · have outside : slot < offset ∨ stop ≤ slot := by omega
        have unchanged : dst'[slot]! = dst[slot]! :=
          block_frame scratch table degree first offset stop dst slot (by omega) ordered outside
        rw [unchanged]
        have same : (stop ≤ slot) ↔ (offset ≤ slot) := by omega
        simp only [same]
    · simp only [scanBlocks, active, ite_false, ite_eq_right (by omega : ¬offset ≤ slot), add_zero]


noncomputable def lowValue (input : Slice U64) (degree slot : Nat) : Field :=
  if slot % 2 = 0 ∧ slot / 2 < input.length ∧ slot / 2 < firstHigh degree
  then toField input[slot / 2]!.bv ^ 2 else 0

private theorem seed_low_value (input dst : Slice U64) (scratch : Slice Raw) (slot : Nat)
    (active : slot < dst.length) :
    toField (seed input 0 (firstHigh dst.length) (RebuiltLfsr.zeroWords dst) scratch input.length).1[slot]!.bv =
      lowValue input dst.length slot := by
  have zeroLength : (RebuiltLfsr.zeroWords dst).length = dst.length := by simp [RebuiltLfsr.zeroWords, Slice.length]
  rw [dst_seed_word input (RebuiltLfsr.zeroWords dst) scratch 0 input.length (firstHigh dst.length) slot
    (by rwa [zeroLength])]
  have zeroWord : (RebuiltLfsr.zeroWords dst)[slot]! = 0#u64 := by
    rw [Slice.getElem!_Nat_eq, RebuiltLfsr.zeroWords, Slice.from_val]
    rw [List.getElem!_replicate]
    exact active
  simp only [Nat.zero_le, Nat.zero_add, true_and, lowValue]
  split
  · exact toField_square _
  · rw [zeroWord]
    exact toField_zero

noncomputable def sourceHighValue (input table : Slice U64) (degree slot : Nat) : Field :=
  let first := firstHigh degree
  ∑ i ∈ Finset.range (input.length - first),
    toField input[first + i]!.bv ^ 2 * toField (tableRow table degree i)[slot]!.bv

private theorem seed_high_value (input table dst : Slice U64) (scratch : Slice Raw) (slot : Nat)
    (scratchRoom : input.length ≤ scratch.length) :
    let first := firstHigh dst.length
    let squared := (seed input 0 first (RebuiltLfsr.zeroWords dst) scratch input.length).2
    highValue (DenseMul.takeSlice squared input.length) table dst.length first slot =
      sourceHighValue input table dst.length slot := by
  let first := firstHigh dst.length
  let squared := (seed input 0 first (RebuiltLfsr.zeroWords dst) scratch input.length).2
  have width : squared.length = scratch.length := seed_scratch_length ..
  have prefixWidth : (DenseMul.takeSlice squared input.length).length = input.length := by
    simp only [DenseMul.take_length, width, Nat.min_eq_left scratchRoom]
  unfold highValue sourceHighValue
  dsimp only
  rw [show (DenseMul.takeSlice squared input.length).length = input.length from prefixWidth]
  apply Finset.sum_congr rfl
  intro i member
  have active : first + i < input.length := by
    have index := Finset.mem_range.mp member
    omega
  change scratchTerm (DenseMul.takeSlice squared input.length) table dst.length first (first + i) slot = _
  unfold scratchTerm
  rw [DenseMul.take_word _ _ _ active, scratch_seed_word input (RebuiltLfsr.zeroWords dst) scratch 0
    input.length first (first + i) (by omega), ite_eq_left (by omega), Nat.add_sub_cancel_left]
  exact congrArg (fun word => word * toField (tableRow table dst.length i)[slot]!.bv) (toField_square _)

private theorem reduce_square_coeff (input modulus table : Slice U64) (degree slot : Nat)
    (inputBound : input.length ≤ degree) (inside : slot < degree) (valid : CorrectTable modulus table degree) :
    (reduceSquare input table degree).coeff slot = lowValue input degree slot + sourceHighValue input table degree slot := by
  let first := firstHigh degree
  let h := min first input.length
  let term := fun i =>
    (C ((slicePolynomial input).coeff i ^ 2) *
      (if i < first then X ^ (2 * i) else
        slicePolynomial (tableRow table degree (i - first)))).coeff slot
  have hLe : h ≤ input.length := Nat.min_le_right _ _
  have hFirst : h ≤ first := Nat.min_le_left _ _
  have lenSplit : h + (input.length - h) = input.length := Nat.add_sub_of_le hLe
  have lowNormal (i : Nat) (iBound : i < h) :
      term i = (if slot = 2 * i then toField input[i]!.bv ^ 2 else 0) := by
    unfold term
    rw [ite_eq_left (by omega), coeff_C_mul, coeff_X_pow, slicePolynomial_coeff, ite_eq_left (by omega)]
    split <;> simp
  have lowSum : (∑ i ∈ Finset.range h, term i) = lowValue input degree slot := by
    unfold lowValue
    by_cases hit : slot % 2 = 0 ∧ slot / 2 < input.length ∧ slot / 2 < firstHigh degree
    · have hBound : slot / 2 < h := Nat.lt_min.mpr ⟨hit.2.2, hit.2.1⟩
      rw [ite_eq_left hit, Finset.sum_eq_single (slot / 2)]
      · rw [lowNormal _ hBound, ite_eq_left (by omega)]
      · intro j member ne
        have bound := Finset.mem_range.mp member
        rw [lowNormal _ bound, ite_eq_right (by omega)]
      · intro absent
        exact (absent (Finset.mem_range.mpr hBound)).elim
    · rw [ite_eq_right hit]
      apply Finset.sum_eq_zero
      intro i member
      have bound := Finset.mem_range.mp member
      rw [lowNormal _ bound, ite_eq_right]
      intro equality
      have src : i < input.length := bound.trans_le hLe
      have lower : i < firstHigh degree := bound.trans_le hFirst
      exact hit ⟨by omega, by omega, by omega⟩
  have highSum : (∑ i ∈ Finset.range (input.length - h), term (h + i)) = sourceHighValue input table degree slot := by
    by_cases enough : first ≤ input.length
    · have hEq : h = first := Nat.min_eq_left enough
      rw [hEq]
      unfold sourceHighValue
      apply Finset.sum_congr rfl
      intro i member
      have index : i < input.length - first := Finset.mem_range.mp member
      have rowBound : i < degree / 2 := by unfold first firstHigh at *; omega
      have coeff := slicePolynomial_coeff (tableRow table degree i) slot
      rw [table_row_length modulus table degree i valid rowBound, ite_eq_left inside] at coeff
      unfold term
      rw [ite_eq_right (by omega), Nat.add_sub_cancel_left, coeff_C_mul, coeff,
        slicePolynomial_coeff, ite_eq_left (by omega)]
    · have hEq : h = input.length := Nat.min_eq_right (by omega)
      have noHigh : input.length - first = 0 := by omega
      simp only [hEq, Nat.sub_self, Finset.range_zero, Finset.sum_empty, sourceHighValue, show
        input.length - firstHigh degree = 0 from noHigh]
  rw [reduceSquare, finsetSum_coeff]
  change (∑ i ∈ Finset.range input.length, term i) = _
  rw [← lenSplit, Finset.sum_range_add, lowSum, highSum]

/-- The complete original AVX slice result computes the same monic
remainder as Dense's scalar fallback. This theorem is independent of
the source memory law used to produce the result. -/
theorem square_result_remainder (input modulus table dst : Slice U64) (scratch : Slice Raw)
    (aBound : input.length ≤ dst.length) (scratchRoom : input.length ≤ scratch.length)
    (shape : modulus.length = dst.length + 1) (monic : modulus[dst.length]! = 1#u64)
    (valid : CorrectTable modulus table dst.length) :
    slicePolynomial (squareResult input table dst scratch).1 =
      slicePolynomial input ^ 2 %ₘ slicePolynomial modulus := by
  rw [← square_remainder input modulus table dst.length shape monic aBound valid]
  ext slot
  have dstLength := (square_result_lengths input table dst scratch).1
  rw [slicePolynomial_coeff, dstLength]
  by_cases active : slot < dst.length
  · rw [ite_eq_left active, reduce_square_coeff input modulus table dst.length slot aBound active valid]
    let first := firstHigh dst.length
    let state := seed input 0 first (RebuiltLfsr.zeroWords dst) scratch input.length
    let squared := DenseMul.takeSlice state.2 input.length
    have seedLen : state.1.length = dst.length := by
      simp [state, RebuiltLfsr.zeroWords, Slice.length, seed_dst_length]
    have inputBound : squared.length ≤ dst.length := by
      simp only [squared, DenseMul.take_length]
      omega
    have tableBound : dst.length / 2 * dst.length ≤ table.length := by
      simpa only [Nat.mul_comm] using valid.room
    change toField (scanBlocks squared table dst.length first 0 state.1 dst.length)[slot]!.bv = _
    rw [scanned_blocks_field squared table dst.length first 0 state.1 dst.length slot seedLen inputBound rfl
      tableBound active (by omega), ite_eq_left (Nat.zero_le _)]
    exact congrArg₂ (· + ·) (seed_low_value input dst scratch slot active)
      (seed_high_value input table dst scratch slot scratchRoom)
  · rw [ite_eq_right active]
    exact ((degree_lt_iff_coeff_zero _ _).mp (square_degree input modulus table dst.length aBound valid)
      slot (by omega)).symm

open Aeneas.Std.AvxSquareRuntime
open bulksketch.backend.x86_vpclmul512

/-- The original free accelerated body satisfies the polynomial remainder
law and preserves both borrowed slice widths. -/
def ActualAvxSquareRemainder : Prop :=
  ∀ (loadModel : Load) (storeModel : Store), LoadLaw loadModel → StoreLaw storeModel →
    ∀ (input modulus table dst : Slice U64) (scratch : Slice Raw),
      input.length ≤ dst.length → input.length ≤ scratch.length →
      dst.length + 8 ≤ Usize.max →
      modulus.length = dst.length + 1 → modulus[dst.length]! = 1#u64 →
      CorrectTable modulus table dst.length →
      ∃ output rawOut,
        square_mod loadModel storeModel input table dst scratch = .ok (output, rawOut) ∧
        output.length = dst.length ∧ rawOut.length = scratch.length ∧
        slicePolynomial output = slicePolynomial input ^ 2 %ₘ slicePolynomial modulus

theorem square_mod_remainder : ActualAvxSquareRemainder := by
  intro loadModel storeModel loadLaw storeLaw input modulus table dst scratch
    aRoom scratchRoom safe shape monic valid
  have tableBound : dst.length / 2 * dst.length ≤ table.length := by
    simpa only [Nat.mul_comm] using valid.room
  let expected := squareResult input table dst scratch
  exact ⟨expected.1, expected.2,
    square_mod_refines loadModel storeModel loadLaw storeLaw input table dst scratch aRoom scratchRoom safe tableBound,
    (square_result_lengths input table dst scratch).1, (square_result_lengths input table dst scratch).2,
    square_result_remainder input modulus table dst scratch aRoom scratchRoom shape monic valid⟩

/-- The true dispatch branch links the AVX free body to Dense's backend
law. The trait selector's correspondence is an explicit premise. -/
theorem backend_law_of_dispatch {K : Type} (kernels : bulksketch.backend.contract.BulkKernels K bulksketch.field.Gf64)
    (loadModel : Load) (storeModel : Store) (loadLaw : LoadLaw loadModel) (storeLaw : StoreLaw storeModel)
    (modulus table : Slice U64) (degree : Nat)
    (shape : modulus.length = degree + 1) (monic : modulus[degree]! = 1#u64)
    (valid : CorrectTable modulus table degree)
    (dispatch : ∀ (input dst : Slice U64) (scratch : Slice Raw),
      kernels.square_mod input table dst scratch =
        (do
          let (output, updated) ← square_mod loadModel storeModel input table dst scratch
          .ok (true, output, updated))) :
    DenseReducerSquare.BackendSquareLaw kernels modulus table degree := by
  intro input dst scratch inputRoom width rawRoom
  have maximum : scratch.length ≤ Usize.max := scratch.length_ineq
  have sixteen : 16 ≤ Usize.max := by
    simp only [Usize.max, Usize.numBits]
    rcases System.Platform.numBits_eq with bits | bits <;> simp [bits]
  have safe : dst.length + 8 ≤ Usize.max := by omega
  obtain ⟨output, updated, normal, length, rawLength, remainder⟩ :=
    square_mod_remainder loadModel storeModel loadLaw storeLaw input modulus table dst scratch
      (by omega) (by omega) safe (by omega) (by rwa [width]) (width ▸ valid)
  refine ⟨true, output, updated, ?_, length.trans width, rawLength, fun _ => remainder⟩
  rw [dispatch, normal]
  simp only [bind_ok]
  rfl

open X86MaskedMemory X86MaskedMemory.Allocation X86MaskedMemory.Llbc

/-- The slice-level load used by the projected square is the exact result
of the original masked-load LLBC on a witnessed allocation view. -/
theorem square_load_allocated (live : LiveAllocations) (la57 : Bool) (heap : AddressHeap)
    (base : Address) (words : Slice U64) (permit : Address → Bool)
    (bound : words.length ≤ 8) (view : ReadView live la57 heap base (8 * words.length) 8)
    (bytes : FiniteWordWindow heap base words.length (fun index => words[index]!.bv)) :
    exec (liftPermission permit) loadProgram (loadInput (liftHeap heap) ⟨base.toNat, words.len⟩) =
      some (.register (loadWords words), liftHeap heap) :=
  allocated_load_refines live la57 heap base words permit bound view bytes

/-- The original masked-store LLBC returns exactly the projected
square's destination words and preserves bytes outside the active block. -/
theorem square_store_allocated (live : LiveAllocations) (la57 : Bool) (heap : AddressHeap)
    (base : Address) (words : Slice U64) (permit : Address → Bool) (value : Word512)
    (bound : words.length ≤ 8) (view : WriteView live la57 heap permit base (8 * words.length) 8) :
    ∃ updated : AddressHeap,
      exec (liftPermission permit) storeProgram (storeInput (liftHeap heap) ⟨base.toNat, words.len⟩ value) =
        some (.unit, liftHeap updated) ∧
      FiniteWordWindow updated base words.length (fun i => (storeWords words value bound)[i]!.bv) ∧
      ∀ address, address.toNat < base.toNat ∨ base.toNat + 8 * words.length ≤ address.toNat →
        updated address = heap address := by
  have admitted : words.len.val ≤ 8 := by rwa [Slice.len_val]
  have admittedView : WriteView live la57 heap permit base (8 * words.len.val) 8 := by rwa [Slice.len_val]
  obtain ⟨updated, normal, written, frame⟩ :=
    allocated_store_refines live la57 heap base words.len permit value admitted admittedView
  refine ⟨updated, normal, ?_, ?_⟩
  · intro index active byte
    let lane : Fin 8 := ⟨index, by omega⟩
    have stored := written lane byte (by simpa only [lane, Slice.len_val] using active)
    dsimp only
    rw [store_word words value bound index active]
    exact stored
  · simpa only [Slice.len_val] using frame

end BulksketchBridge.AvxSquare
