import BulksketchBridge.VerifyDispatchSpec

namespace BulksketchBridge.VerifyDispatch

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open bulksketch.decode.verify

private theorem val_word {n : Nat} (bound : n ≤ U64.max) : (toWord n).val = n := by
  rw [U64.max_eq] at bound
  change n % 18446744073709551616 = n
  exact Nat.mod_eq_of_lt (by omega)

private theorem word_of_val (word : U64) : toWord word.val = word := by
  apply UScalar.eq_of_val_eq
  exact val_word (by simpa only [U64.max_eq] using word.le_max)

private theorem result_word {result : Result U64} {n : Nat}
    (specification : result ⦃ word => word.val = n ⦄) :
    result = Result.ok (toWord n) := by
  cases result using Result.cases with
  | ret word =>
    have value := (spec_ok word).mp specification
    rw [← value, word_of_val]
  | vis effect k => simp only [spec_vis] at specification
  | div => simp only [spec_div] at specification

private theorem add_word {x y : Nat} (bound : x + y ≤ U64.max) :
    toWord x + toWord y = Result.ok (toWord (x + y)) := by
  have hx := val_word (n := x) (by omega)
  have hy := val_word (n := y) (by omega)
  apply result_word
  simpa only [hx, hy] using
    U64.add_spec (x := toWord x) (y := toWord y) (by simpa only [hx, hy] using bound)

private theorem mul_word {x y : Nat}
    (hx : x ≤ U64.max) (hy : y ≤ U64.max) (bound : x * y ≤ U64.max) :
    toWord x * toWord y = Result.ok (toWord (x * y)) := by
  apply result_word
  simpa only [val_word hx, val_word hy] using
    U64.mul_spec (x := toWord x) (y := toWord y)
      (by simpa only [val_word hx, val_word hy] using bound)

private theorem div_word {x y : Nat} (hx : x ≤ U64.max) (hy : y ≤ U64.max) (pos : y ≠ 0) :
    toWord x / toWord y = Result.ok (toWord (x / y)) := by
  apply result_word
  simpa only [val_word hx, val_word hy] using
    U64.div_spec (toWord x) (y := toWord y) (by simpa only [val_word hy] using pos)

private theorem rem_word {x y : Nat} (hx : x ≤ U64.max) (hy : y ≤ U64.max) (pos : y ≠ 0) :
    toWord x % toWord y = Result.ok (toWord (x % y)) := by
  apply result_word
  simpa only [val_word hx, val_word hy] using
    UScalar.rem_spec (toWord x) (y := toWord y) (by simpa only [val_word hy] using pos)

private theorem sub_word {x y : Nat} (hx : x ≤ U64.max) (h : y ≤ x) :
    toWord x - toWord y = Result.ok (toWord (x - y)) := by
  have hy : y ≤ U64.max := by omega
  apply result_word
  apply spec_mono (U64.sub_spec (x := toWord x) (y := toWord y)
    (by simpa only [val_word hx, val_word hy] using h))
  intro out value
  simpa only [val_word hx, val_word hy] using value.1

private theorem div_ceil_eight {x : Nat} (bound : x ≤ 65535) :
    core.num.U64.div_ceil (toWord x) (toWord 8) = Result.ok (toWord ((x + 7) / 8)) := by
  have hx : x ≤ U64.max := by rw [U64.max_eq]; omega
  have hr : x % 8 ≤ U64.max := by rw [U64.max_eq]; omega
  have addBound : x / 8 + 1 ≤ U64.max := by rw [U64.max_eq]; omega
  simp only [core.num.U64.div_ceil, div_word (y := 8) hx (by rw [U64.max_eq]; decide) (by decide),
    rem_word (y := 8) hx (by rw [U64.max_eq]; decide) (by decide), bind_ok, UScalar.lt_equiv, val_word hr]
  change (if 0 < x % 8 then toWord (x / 8) + toWord 1 else Result.ok (toWord (x / 8))) = _
  rw [add_word addBound]
  split <;> congr 2 <;> omega

set_option linter.auxLemma false in
private theorem tail_refines (remainder : U64) :
    (product_counts.match_2 (fun _ => Result U64) remainder (fun _ => ok 0#u64) (fun _ =>
          if 1#u64 <= remainder
          then
            if remainder <= 8#u64
            then ok 1#u64
            else
              if 9#u64 <= remainder
              then if remainder <= 16#u64
                   then ok 2#u64
                   else ok 4#u64
              else ok 4#u64
          else
            if 9#u64 <= remainder
            then if remainder <= 16#u64
                 then ok 2#u64
                 else ok 4#u64
            else ok 4#u64)) = Result.ok (toWord (tailVectors remainder.val)) := by
  split
  · rfl
  · rename_i notZero
    have positive : 1 ≤ remainder.val := by
      by_contra! h
      exact notZero (UScalar.eq_of_val_eq (by change remainder.val = 0; omega))
    have valNonzero : remainder.val ≠ 0 := by omega
    simp only [tailVectors, valNonzero, ite_false, UScalar.le_equiv]
    change (if 1 ≤ remainder.val then
      if remainder.val ≤ 8 then ok 1#u64
      else if 9 ≤ remainder.val then
        if remainder.val ≤ 16 then ok 2#u64 else ok 4#u64
      else ok 4#u64
    else if 9 ≤ remainder.val then
      if remainder.val ≤ 16 then ok 2#u64 else ok 4#u64
    else ok 4#u64) = _
    by_cases eight : remainder.val ≤ 8
    · simp only [positive, eight, ite_true]
      rfl
    · have nine : 9 ≤ remainder.val := by omega
      simp only [positive, eight, nine, ite_true, ite_false]
      split <;> rfl

private theorem cast_word (x : Usize) (bound : x.val ≤ 65535) :
    UScalar.cast .U64 x = toWord x.val := by
  apply UScalar.eq_of_val_eq
  rw [UScalar.cast_val_mod_pow_of_inBounds_eq, val_word]
  · rw [U64.max_eq]; omega
  · change x.val < 18446744073709551616
    omega

private theorem size_limit : (core.convert.num.FromUsizeU16.from core.num.U16.MAX).val =
    65535 := by
  rw [core.convert.num.FromUsizeU16.from_val_eq]
  rfl

theorem product_counts_refines : ProductCountsRefines := by
  intro degree capacity
  unfold product_counts expectedCounts
  simp only [UScalar.lt_equiv]
  by_cases order : degree.val ≤ capacity.val
  · rw [ite_eq_right (by omega : ¬ capacity.val < degree.val)]
    simp only [lift, bind_ok, size_limit]
    by_cases limit : capacity.val ≤ 65535
    · rw [ite_eq_right (by omega : ¬ 65535 < capacity.val), ite_eq_left ⟨order, limit⟩]
      have degreeBound : degree.val ≤ U64.max := by rw [U64.max_eq]; omega
      have w32 : 32#u64 = toWord 32 := rfl
      simp only [w32, cast_word degree (by omega : degree.val ≤ 65535), cast_word capacity limit, bind_ok,
        div_word (y := 32) degreeBound (by rw [U64.max_eq]; decide) (by decide),
        rem_word (y := 32) degreeBound (by rw [U64.max_eq]; decide) (by decide), tail_refines]
      have remBound : degree.val % 32 ≤ U64.max := by rw [U64.max_eq]; omega
      simp only [val_word remBound]
      unfold counts
      dsimp only
      have w8 : 8#u64 = toWord 8 := rfl
      have w4 : 4#u64 = toWord 4 := rfl
      have w3 : 3#u64 = toWord 3 := rfl
      have w2 : 2#u64 = toWord 2 := rfl
      have w1 : 1#u64 = toWord 1 := rfl
      have w0 : 0#u64 = toWord 0 := rfl
      simp only [w8, w4, w3, w2, w1, w0,
        div_word (y := 8) degreeBound (by rw [U64.max_eq]; decide) (by decide),
        rem_word (y := 8) degreeBound (by rw [U64.max_eq]; decide) (by decide),
        sub_word (by rw [U64.max_eq]; omega : capacity.val ≤ U64.max) order,
        div_ceil_eight (by omega : capacity.val - degree.val ≤ 65535), bind_ok]
      set tail := degree.val % 32
      have tailVal : (toWord tail).val = tail := val_word remBound
      have sixteen : (16#u64 : U64).val = 16 := rfl
      simp only [UScalar.le_equiv, tailVal, sixteen, ← apply_ite (fun n => ok (toWord n))]
      set small := if tail ≤ 16 then tailVectors tail else 0
      set tailCount := tailVectors tail
      have tailBound : tailCount ≤ 4 := by unfold tailCount tailVectors; split_ifs <;> decide
      have smallBound : small ≤ 4 := by unfold small; split <;> omega
      set tiles := degree.val / 32
      have tilesBound : tiles ≤ 2047 := by unfold tiles; omega
      set blocks := degree.val / 8
      have blocksBound : blocks ≤ 8191 := by unfold blocks; omega
      set tail8 := degree.val % 8
      have tail8Bound : tail8 ≤ 7 := by unfold tail8; omega
      set continuation := (capacity.val - degree.val + 7) / 8
      have continuationBound : continuation ≤ 8192 := by unfold continuation; omega
      have w6 : 6#u64 = toWord 6 := rfl
      have vectorsBound : 4 * tiles + tailCount ≤ 8192 := by omega
      have reductionsBound : 2 * (4 * tiles + tailCount) + 4 * small ≤ 16400 := by omega
      have currentRaw := Nat.mul_le_mul (by omega : 2 * (4 * tiles + tailCount) ≤ 16384) limit
      have currentReduced := Nat.mul_le_mul reductionsBound limit
      have locatorMain := Nat.mul_le_mul (by omega : 4 * blocks ≤ 32764)
        (by omega : blocks + 1 ≤ 8192)
      have locatorTail := Nat.mul_le_mul (by omega : blocks + 1 ≤ 8192) tail8Bound
      have locatorBound : 4 * blocks * (blocks + 1) + (blocks + 1) * tail8 ≤ 268500000 := by omega
      have degreeLimit : degree.val ≤ 65535 := by omega
      have seedRaw := Nat.mul_le_mul vectorsBound degreeLimit
      have seedReduced := Nat.mul_le_mul reductionsBound degreeLimit
      have tailRaw := Nat.mul_le_mul degreeLimit continuationBound
      have tailReduced := Nat.mul_le_mul (by omega : 2 * degree.val + 4 ≤ 131074) continuationBound
      simp (disch := rw [U64.max_eq]; omega) only [w6, mul_word, add_word, bind_ok]
    · rw [ite_eq_left (by omega : 65535 < capacity.val), ite_eq_right (by simp [limit])]
  · rw [ite_eq_left (by omega : capacity.val < degree.val), ite_eq_right (by simp [order])]


private theorem counts_eq (left right : ProductCounts) :
    ProductCounts.Insts.CoreCmpPartialEqProductCounts.eq left right =
      ok (decide (left.raw.val = right.raw.val ∧
        left.including_reduction.val = right.including_reduction.val)) := by
  have scalarEq (a b : U64) : a = b ↔ a.val = b.val := ⟨congrArg UScalar.val, UScalar.eq_of_val_eq⟩
  simp only [ProductCounts.Insts.CoreCmpPartialEqProductCounts.eq, scalarEq]
  split <;> simp_all

theorem use_rebuilt_lfsr_refines : UseRebuiltLfsrRefines := by
  intro degree capacity
  have tiny : (2#usize : Usize).val = 2 := by simp
  have result := product_counts_refines degree capacity
  simp only [use_rebuilt_lfsr, selectsRebuilt, UScalar.le_equiv, tiny, result, bind_ok]
  split
  · rfl
  · cases expectedCounts degree.val capacity.val with
    | none => rfl
    | some pair =>
      obtain ⟨current, rebuilt⟩ := pair
      simp only [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
        counts_eq]
      dsimp! only
      split <;> try split
      all_goals
        try simp only [Bind.bind, bind_ok]
        apply congrArg ok
        apply Bool.eq_iff_iff.mpr
        simp
        omega

end BulksketchBridge.VerifyDispatch
