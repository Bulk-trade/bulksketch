import BulksketchBridge.AffinePreferred
import BulksketchBridge.AffineSelector

namespace BulksketchBridge.AffinePreferred

open Aeneas Aeneas.Std Result ControlFlow
open bulksketch.decode.affine
open AffineSelector (word word_val)

private theorem word_eq (x : U64) (value : Nat) (eq : x.val = value) : x = word value := by
  apply UScalar.eq_of_val_eq
  have fits : x.val ≤ U64.max := by simpa only [U64.max_eq] using x.le_max
  rw [word_val _ (eq ▸ fits), eq]

private theorem add64 (x y : U64) (fits : x.val + y.val ≤ U64.max) :
    (x + y : Result U64) = .ok (word (x.val + y.val)) := by
  obtain ⟨r, normal, val⟩ := RawMulTable.normal_of_spec _ _ (U64.add_spec (x := x) (y := y) fits)
  rw [normal, word_eq _ _ val]

private theorem sub64 (x y : U64) (fits : y.val ≤ x.val) :
    (x - y : Result U64) = .ok (word (x.val - y.val)) := by
  obtain ⟨r, normal, val⟩ := RawMulTable.normal_of_spec _ _ (U64.sub_spec (x := x) (y := y) fits)
  rw [normal, word_eq _ _ val.1]

private theorem mul64 (x y : U64) (fits : x.val * y.val ≤ U64.max) :
    (x * y : Result U64) = .ok (word (x.val * y.val)) := by
  obtain ⟨r, normal, val⟩ := RawMulTable.normal_of_spec _ _ (U64.mul_spec (x := x) (y := y) fits)
  rw [normal, word_eq _ _ val]

private theorem word_small (n : Nat) (bound : n ≤ 131072) : (word n).val = n := by
  apply word_val
  rw [U64.max_eq]
  omega

private theorem ceil8 (x : U64) (small : x.val ≤ 64) :
    core.num.U64.div_ceil x 8#u64 = .ok (word ((x.val + 7) / 8)) := by
  obtain ⟨q, quotient, qval⟩ := RawMulTable.normal_of_spec _ _
    (U64.div_spec x (y := 8#u64) (by decide))
  obtain ⟨r, remainder, rval⟩ := RawMulTable.normal_of_spec _ _
    (UScalar.rem_spec x (y := 8#u64) (by decide))
  change q.val = x.val / 8 at qval
  change r.val = x.val % 8 at rval
  simp only [core.num.U64.div_ceil, quotient, remainder, bind_ok, UScalar.lt_equiv,
    show (0#u64).val = 0 from rfl, rval]
  split
  · rw [add64 _ _ (by rw [qval, U64.max_eq]; change x.val / 8 + 1 ≤ _; omega), qval]
    congr 2
    change x.val / 8 + 1 = _
    omega
  · rw [word_eq _ _ qval]
    congr 2
    omega

private def lanePrice (degree column pivot : Nat) : Nat :=
  2 * ((degree - pivot + 7) / 8 + (column + 8) / 8)

private def pivotTail (degree column : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, pivot => lanePrice degree column pivot + pivotTail degree column n (pivot + 1)

private theorem lane_bound (d c p : Nat) (degree : d < 64) (column : c ≤ d) :
    lanePrice d c p ≤ 32 := by
  unfold lanePrice
  omega

private theorem pivot_bound (d c fuel pivot : Nat) (degree : d < 64) (column : c ≤ d) :
    pivotTail d c fuel pivot ≤ 32 * fuel := by
  induction fuel generalizing pivot with
  | zero => simp [pivotTail]
  | succ n ih =>
    have head := lane_bound d c pivot degree column
    have tail := ih (pivot + 1)
    simp only [pivotTail]
    omega

private theorem pivot_step (d c g p : U64)
    (degree : d.val < 64) (column : c.val ≤ d.val) (live : p.val < c.val)
    (room : g.val + 32 ≤ U64.max) :
    predicted_affine_loop0_loop0.body d c g p =
      .ok (.cont (word (g.val + lanePrice d.val c.val p.val), word (p.val + 1))) := by
  have dsub : (d - p : Result U64) = .ok (word (d.val - p.val)) := sub64 d p (by omega)
  have dsubVal : (word (d.val - p.val)).val = d.val - p.val := word_small _ (by omega)
  have cadd : (c + 1#u64 : Result U64) = .ok (word (c.val + 1)) := by
    apply add64
    rw [U64.max_eq]
    change c.val + 1 ≤ _
    omega
  have caddVal : (word (c.val + 1)).val = c.val + 1 := word_small _ (by omega)
  have left := ceil8 (word (d.val - p.val)) (by rw [dsubVal]; omega)
  have right := ceil8 (word (c.val + 1)) (by rw [caddVal]; omega)
  rw [dsubVal] at left
  rw [caddVal] at right
  have leftVal := word_small ((d.val - p.val + 7) / 8) (by omega)
  have rightVal := word_small ((c.val + 1 + 7) / 8) (by omega)
  simp only [predicted_affine_loop0_loop0.body, UScalar.lt_equiv, live, ite_true,
    dsub, bind_ok, left, cadd, right]
  rw [add64 _ _ (by rw [leftVal, rightVal, U64.max_eq]; omega), bind_ok, leftVal, rightVal]
  have both := word_small ((d.val - p.val + 7) / 8 + (c.val + 1 + 7) / 8) (by omega)
  rw [mul64 _ _ (by rw [both, U64.max_eq]; change 2 * _ ≤ _; omega), bind_ok, both]
  have twice := word_small ((2#u64).val * ((d.val - p.val + 7) / 8 + (c.val + 1 + 7) / 8))
    (by change 2 * _ ≤ _; omega)
  rw [add64 _ _ (by rw [twice]; change g.val + 2 * _ ≤ _; omega), bind_ok, twice,
    add64 _ _ (by rw [U64.max_eq]; change p.val + 1 ≤ _; omega), bind_ok]
  rfl

private theorem pivot_loop (d c : U64) (fuel : Nat) (g p : U64)
    (degree : d.val < 64) (column : c.val ≤ d.val) (remaining : p.val + fuel = c.val)
    (room : g.val + 32 * fuel ≤ U64.max) :
    predicted_affine_loop0_loop0 d g c p =
      .ok (word (g.val + pivotTail d.val c.val fuel p.val)) := by
  induction fuel generalizing g p with
  | zero =>
    have stop : ¬ p.val < c.val := by omega
    rw [predicted_affine_loop0_loop0, loop]
    simp only [predicted_affine_loop0_loop0.body, UScalar.lt_equiv, stop, ite_false, bind_ok,
      pivotTail, Nat.add_zero]
    exact congrArg Result.ok (word_eq _ _ rfl)
  | succ fuel ih =>
    have live : p.val < c.val := by omega
    have next := pivot_step d c g p degree column live (by omega)
    have bound := lane_bound d.val c.val p.val degree column
    have gVal : (word (g.val + lanePrice d.val c.val p.val)).val =
        g.val + lanePrice d.val c.val p.val := word_val _ (by omega)
    have pVal : (word (p.val + 1)).val = p.val + 1 := word_small _ (by omega)
    rw [predicted_affine_loop0_loop0, loop]
    simp only [next, bind_ok]
    change predicted_affine_loop0_loop0 d (word (g.val + lanePrice d.val c.val p.val)) c
      (word (p.val + 1)) = _
    rw [ih _ _ (by rw [pVal]; omega) (by rw [gVal]; omega), gVal, pVal, pivotTail, Nat.add_assoc]

private def columnTail (degree : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, column => pivotTail degree column column 0 + columnTail degree n (column + 1)

private theorem column_loop (d : U64) (fuel : Nat) (g c : U64)
    (degree : d.val < 64) (remaining : c.val + fuel = d.val + 1)
    (room : g.val + 2048 * fuel ≤ U64.max) :
    predicted_affine_loop0 d g c =
      .ok (word (g.val + columnTail d.val fuel c.val)) := by
  induction fuel generalizing g c with
  | zero =>
    have stop : ¬ c.val ≤ d.val := by omega
    rw [predicted_affine_loop0, loop]
    simp only [predicted_affine_loop0.body, UScalar.le_equiv, stop, ite_false, bind_ok,
      columnTail, Nat.add_zero]
    exact congrArg Result.ok (word_eq _ _ rfl)
  | succ fuel ih =>
    have live : c.val ≤ d.val := by omega
    have inner := pivot_loop d c c.val g 0#u64 degree live (by change 0 + c.val = c.val; omega) (by omega)
    change predicted_affine_loop0_loop0 d g c 0#u64 =
      .ok (word (g.val + pivotTail d.val c.val c.val 0)) at inner
    have increment : (c + 1#u64 : Result U64) = .ok (word (c.val + 1)) := by
      apply add64
      rw [U64.max_eq]
      change c.val + 1 ≤ _
      omega
    have next : predicted_affine_loop0.body d g c =
        .ok (.cont (word (g.val + pivotTail d.val c.val c.val 0), word (c.val + 1))) := by
      simp only [predicted_affine_loop0.body, UScalar.le_equiv, live, ite_true, inner, bind_ok,
        increment]
    have bound := pivot_bound d.val c.val c.val 0 degree live
    have gVal : (word (g.val + pivotTail d.val c.val c.val 0)).val =
        g.val + pivotTail d.val c.val c.val 0 := word_val _ (by omega)
    have cVal : (word (c.val + 1)).val = c.val + 1 := word_small _ (by omega)
    rw [predicted_affine_loop0, loop]
    simp only [next, bind_ok]
    change predicted_affine_loop0 d (word (g.val + pivotTail d.val c.val c.val 0))
      (word (c.val + 1)) = _
    rw [ih _ _ (by rw [cVal]; omega) (by rw [gVal]; omega), gVal, cVal, columnTail, Nat.add_assoc]

private theorem pivot_tail_range (d c fuel p : Nat) :
    pivotTail d c fuel p = ((List.range' p fuel).map (lanePrice d c)).sum := by
  induction fuel generalizing p with
  | zero => rfl
  | succ fuel ih =>
    rw [pivotTail, List.range'_succ, List.map_cons, List.sum_cons, ih]

private theorem column_tail_range (d fuel c : Nat) :
    columnTail d fuel c =
      ((List.range' c fuel).map fun i => ((List.range i).map (lanePrice d i)).sum).sum := by
  induction fuel generalizing c with
  | zero => rfl
  | succ fuel ih =>
    rw [columnTail, List.range'_succ, List.map_cons, List.sum_cons, ih, pivot_tail_range,
      ← List.range_eq_range']

private theorem unit_le_degree (d : Nat) (lower : 3 ≤ d) : unitColumns d ≤ d := by
  have lt := Nat.log_lt_self 2 (by omega : d - 1 ≠ 0)
  unfold unitColumns
  omega

/-- The two original nested Gaussian loops return the natural price on the
predictor's entire bounded degree domain. -/
def ActualNativeGaussianPrice : Prop :=
  ∀ d : Nat, 3 ≤ d → d < 64 →
    predicted_affine_loop0 (word d) 0#u64 (word (unitColumns d)) =
      .ok (word (gaussianPrice d))

theorem native_gaussian_price : ActualNativeGaussianPrice := by
  intro d lower upper
  have unit := unit_le_degree d lower
  have dval := word_small d (by omega)
  have uval := word_small (unitColumns d) (by omega)
  rw [column_loop _ (d + 1 - unitColumns d) _ _ (by rw [dval]; exact upper)
    (by rw [dval, uval]; omega) (by rw [U64.max_eq]; change 0 + _ ≤ _; omega),
    dval, uval, show (0#u64).val = 0 from rfl, Nat.zero_add, column_tail_range,
    List.range'_eq_map_range, List.map_map, gaussianPrice]
  rfl

private theorem cast_u64 {ty : UScalarTy} (value : UScalar ty) (small : value.val ≤ 131072) :
    UScalar.cast .U64 value = word value.val := by
  apply UScalar.eq_of_val_eq
  rw [UScalar.cast_val_eq, word_small _ small]
  exact Nat.mod_eq_of_lt (by change value.val < 2 ^ 64; omega)

private theorem platform_bounds : 32 ≤ System.Platform.numBits ∧ System.Platform.numBits ≤ 64 := by
  rcases System.Platform.numBits_eq with bits | bits <;> rw [bits] <;> decide

private theorem leading_value (previous : Usize) (positive : 0 < previous.val) :
    (core.num.Usize.leading_zeros previous).val =
      System.Platform.numBits - Nat.log 2 previous.val - 1 := by
  have nonzero : previous.bv ≠ 0 := by
    intro eq
    have zero := congrArg BitVec.toNat eq
    rw [Usize.bv_toNat] at zero
    change previous.val = 0 at zero
    omega
  have zeros : BitVec.leadingZeros previous.bv =
      System.Platform.numBits - Nat.log 2 previous.val - 1 := by
    unfold BitVec.leadingZeros
    rw [ite_eq_right nonzero, Usize.bv_toNat]
  rw [← U32.bv_toNat]
  change (BitVec.ofNat 32 (BitVec.leadingZeros previous.bv)).toNat = _
  rw [BitVec.toNat_ofNat, zeros]
  exact Nat.mod_eq_of_lt (by have := platform_bounds.2; omega)

private theorem source_bits_value : core.num.Usize.BITS.val = System.Platform.numBits := by
  unfold core.num.Usize.BITS UScalar.ofNat
  exact UScalar.ofNatCore_val_eq _

private theorem unit_width (previous : Usize) (positive : 0 < previous.val) (small : previous.val < 64) :
    ∃ bits : U32,
      (core.num.Usize.BITS - core.num.Usize.leading_zeros previous : Result U32) = .ok bits ∧
      bits.val = 1 + Nat.log 2 previous.val := by
  have upper := (Nat.log_lt_iff_lt_pow (by decide : 1 < 2) (by omega : previous.val ≠ 0)).mpr
    (show previous.val < 2 ^ 6 from small)
  have zeros := leading_value previous positive
  have width := platform_bounds.1
  obtain ⟨bits, normal, val⟩ := RawMulTable.normal_of_spec _ _
    (U32.sub_spec (x := core.num.Usize.BITS) (y := core.num.Usize.leading_zeros previous)
      (by rw [zeros, source_bits_value]; omega))
  refine ⟨bits, normal, ?_⟩
  rw [val.1, zeros, source_bits_value]
  omega

private theorem source_unit_columns (degree previous : Usize) (lower : 3 ≤ degree.val)
    (upper : degree.val < 64) (prior : previous.val = degree.val - 1) :
    ∃ bits : U32,
      (core.num.Usize.BITS - core.num.Usize.leading_zeros previous : Result U32) = .ok bits ∧
      (1#u64 + UScalar.cast .U64 bits : Result U64) = .ok (word (unitColumns degree.val)) := by
  obtain ⟨bits, normal, val⟩ := unit_width previous (by omega) (by omega)
  have unit := unit_le_degree degree.val lower
  have bitsSmall : bits.val ≤ 131072 := by rw [val, prior]; unfold unitColumns at unit; omega
  have cast := cast_u64 bits bitsSmall
  have castVal : (UScalar.cast .U64 bits).val = bits.val := by rw [cast, word_small _ bitsSmall]
  refine ⟨bits, normal, ?_⟩
  rw [add64 _ _ (by rw [castVal, U64.max_eq]; change 1 + bits.val ≤ _; omega), castVal, val, prior]
  change ok (word (1 + (1 + Nat.log 2 (degree.val - 1)))) = ok (word (unitColumns degree.val))
  congr 2
  unfold unitColumns
  omega

private theorem column_bound (d fuel c : Nat) (degree : d < 64) (remaining : c + fuel ≤ d + 1) :
    columnTail d fuel c ≤ 2048 * fuel := by
  induction fuel generalizing c with
  | zero => simp [columnTail]
  | succ fuel ih =>
    have live : c ≤ d := by omega
    have head := pivot_bound d c c 0 degree live
    have tail := ih (c + 1) (by omega)
    simp only [columnTail]
    omega

private theorem gaussian_bound (d : Nat) (lower : 3 ≤ d) (upper : d < 64) :
    gaussianPrice d ≤ 131072 := by
  have unit := unit_le_degree d lower
  have total := column_bound d (d + 1 - unitColumns d) (unitColumns d) upper (by omega)
  rw [column_tail_range, List.range'_eq_map_range, List.map_map] at total
  change gaussianPrice d ≤ _ at total
  omega

private theorem word_add (x y : Nat) (sum : x + y ≤ U64.max) :
    (word x + word y : Result U64) = .ok (word (x + y)) := by
  have xv := word_val x (by omega)
  have yv := word_val y (by omega)
  rw [add64 _ _ (by rw [xv, yv]; exact sum), xv, yv]

private theorem word_mul (x y : Nat) (xl : x ≤ U64.max) (yl : y ≤ U64.max)
    (product : x * y ≤ U64.max) : (word x * word y : Result U64) = .ok (word (x * y)) := by
  have xv := word_val x xl
  have yv := word_val y yl
  rw [mul64 _ _ (by rw [xv, yv]; exact product), xv, yv]

private theorem word_sub (x y : Nat) (xl : x ≤ U64.max) (yLe : y ≤ x) :
    (word x - word y : Result U64) = .ok (word (x - y)) := by
  have xv := word_val x xl
  have yv := word_val y (yLe.trans xl)
  rw [sub64 _ _ (by rw [xv, yv]; exact yLe), xv, yv]

set_option maxHeartbeats 2500000 in
private theorem predictor_live (degree : Usize) (lower : 3 ≤ degree.val) (upper : degree.val < 64) :
    predicted_affine degree = .ok (predicts degree.val) := by
  have one : (1#usize).val = 1 := Usize.ofNatCore_val_eq _
  have three : (3#usize).val = 3 := Usize.ofNatCore_val_eq _
  have sixtyFour : (64#usize).val = 64 := Usize.ofNatCore_val_eq _
  have notLow : ¬ degree.val < 3 := by omega
  have notHigh : ¬ 64 ≤ degree.val := by omega
  let d := degree.val
  let u := unitColumns d
  let g := gaussianPrice d
  let n := (3 * d) * (d + 1)
  let i := 28 * (d - u)
  let m := 16 * d
  let s := (6 * d) * (d - 1)
  let q := AffineSelector.squareCount d
  have dlo : 3 ≤ d := lower
  have dhi : d < 64 := upper
  have ubd : u ≤ d := unit_le_degree d dlo
  have gbd : g ≤ 131072 := gaussian_bound d dlo dhi
  have nbd : n ≤ 192 * 64 := Nat.mul_le_mul (by omega) (by omega)
  have ibd : i ≤ 28 * 64 := Nat.mul_le_mul_left _ (by omega)
  have mbd : m ≤ 16 * 64 := Nat.mul_le_mul_left _ (by omega)
  have sbd : s ≤ 384 * 64 := Nat.mul_le_mul (by omega) (by omega)
  have qbd : q ≤ 704 := by
    have product : (2 * (d / 2)) * ((d + 7) / 8) ≤ 64 * 8 :=
      Nat.mul_le_mul (by omega) (by omega)
    unfold q AffineSelector.squareCount
    omega
  have rbd : (64 - d) * q ≤ 64 * 704 := Nat.mul_le_mul (Nat.sub_le ..) qbd
  have valU := word_small u (by omega)
  have valD := word_small d (by omega)
  have bound := cast_u64 degree (by omega)
  obtain ⟨previous, sub, prevVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.sub_spec (x := degree) (y := 1#usize) (by rw [one]; omega))
  obtain ⟨bits, bitsNormal, unitNormal⟩ := source_unit_columns degree previous lower upper
    (by rw [prevVal.1, one])
  have pivot : core.num.U64.saturating_sub (word d) (word u) = word (d - u) := by
    unfold core.num.U64.saturating_sub UScalar.saturating_sub
    rw [valD, valU, Nat.zero_max]
    rfl
  have square : square_products (word d) = .ok (word q) := by
    rw [AffineSelector.square_products_refines, valD, AffineSelector.checked]
    exact ite_eq_left (by rw [U64.max_eq]; omega)
  simp only [predicted_affine, UScalar.lt_equiv, UScalar.le_equiv, three, sixtyFour, notLow, notHigh,
    ite_false, lift, bind_ok, bound, sub, bitsNormal, unitNormal]
  rw [native_gaussian_price degree.val lower upper, bind_ok,
    show core.num.U64.saturating_sub (word degree.val) (word (unitColumns degree.val)) = word (d - u) from pivot,
    show square_products (word degree.val) = .ok (word q) from square]
  simp only [bind_ok]
  change (do
    let i4 ← word 3 * word d
    let i5 ← word d + word 1
    let normalization ← i4 * i5
    let inverses ← word 28 * word (d - u)
    let map ← word 16 * word d
    let i6 ← word 6 * word d
    let i7 ← word d - word 1
    let subspaces ← i6 * i7
    let i8 ← word g + normalization
    let i9 ← i8 + inverses
    let i10 ← i9 + map
    let i11 ← i10 + subspaces
    let i12 ← word 64 - word d
    let i14 ← i12 * word q
    .ok (decide (i11.val < i14.val)) : Result Bool) = .ok (predicts d)
  simp only [
    word_mul 3 d (by rw [U64.max_eq]; decide) (by rw [U64.max_eq]; omega)
      (by rw [U64.max_eq]; omega),
    word_add d 1 (by rw [U64.max_eq]; omega),
    word_mul (3 * d) (d + 1) (by rw [U64.max_eq]; omega) (by rw [U64.max_eq]; omega)
      (by change n ≤ _; rw [U64.max_eq]; omega),
    word_mul 28 (d - u) (by rw [U64.max_eq]; decide) (by rw [U64.max_eq]; omega)
      (by change i ≤ _; rw [U64.max_eq]; omega),
    word_mul 16 d (by rw [U64.max_eq]; decide) (by rw [U64.max_eq]; omega)
      (by change m ≤ _; rw [U64.max_eq]; omega),
    word_mul 6 d (by rw [U64.max_eq]; decide) (by rw [U64.max_eq]; omega)
      (by rw [U64.max_eq]; omega),
    word_sub d 1 (by rw [U64.max_eq]; omega) (by omega),
    word_mul (6 * d) (d - 1) (by rw [U64.max_eq]; omega) (by rw [U64.max_eq]; omega)
      (by change s ≤ _; rw [U64.max_eq]; omega),
    bind_ok]
  change (do
    let i8 ← word g + word n
    let i9 ← i8 + word i
    let i10 ← i9 + word m
    let i11 ← i10 + word s
    let i12 ← word 64 - word d
    let i14 ← i12 * word q
    .ok (decide (i11.val < i14.val)) : Result Bool) = .ok (predicts d)
  simp only [
    word_add g n (by rw [U64.max_eq]; omega),
    word_add (g + n) i (by rw [U64.max_eq]; omega),
    word_add (g + n + i) m (by rw [U64.max_eq]; omega),
    word_add (g + n + i + m) s (by rw [U64.max_eq]; omega),
    word_sub 64 d (by rw [U64.max_eq]; decide) (by omega),
    word_mul (64 - d) q (by rw [U64.max_eq]; omega) (by rw [U64.max_eq]; omega)
      (by rw [U64.max_eq]; omega),
    bind_ok,
    word_val (g + n + i + m + s) (by rw [U64.max_eq]; omega),
    word_val ((64 - d) * q) (by rw [U64.max_eq]; omega)]
  rfl

/-- The original predictor returns its exact operation-count comparison on
the live domain and returns false on both guard exits. -/
def ActualNativeAffinePrediction : Prop :=
  ∀ degree : Usize, predicted_affine degree =
    .ok (if 3 ≤ degree.val ∧ degree.val < 64 then predicts degree.val else false)

theorem native_affine_prediction : ActualNativeAffinePrediction := by
  intro degree
  by_cases low : degree.val < 3
  · have no : ¬ (3 ≤ degree.val ∧ degree.val < 64) := by omega
    simp only [predicted_affine, UScalar.lt_equiv, show (3#usize).val = 3 from Usize.ofNatCore_val_eq _,
      low, ite_true, no, ite_false]
  · by_cases high : 64 ≤ degree.val
    · have no : ¬ (3 ≤ degree.val ∧ degree.val < 64) := by omega
      simp only [predicted_affine, UScalar.lt_equiv, UScalar.le_equiv,
        show (3#usize).val = 3 from Usize.ofNatCore_val_eq _,
        show (64#usize).val = 64 from Usize.ofNatCore_val_eq _,
        low, high, ite_true, no, ite_false]
    · have live : 3 ≤ degree.val ∧ degree.val < 64 := by omega
      rw [ite_eq_left live]
      exact predictor_live degree live.1 live.2

/-- The native compile-time mask and the entire GF64 runtime selection domain. -/
def ActualNativePreferred : Prop :=
  PREFERRED_MASK = .ok 524280#u64 ∧
  ∀ degree : Usize, preferred RootSetup.gf64Dictionary degree =
    .ok (decide (3 ≤ degree.val ∧ degree.val ≤ 18))

theorem native_preferred_refines : ActualNativePreferred :=
  native_preferred_under_predictor predictor_live

/-- Standalone frozen proposition for the original compile-time mask. -/
def ActualNativePreferredMask : Prop :=
  PREFERRED_MASK = .ok 524280#u64

theorem native_preferred_mask : ActualNativePreferredMask :=
  native_preferred_refines.1

/-- Discharges the exact source preference premise at the original traversal
entry, including the older protocol's short circuit. -/
theorem root_start_preference (roots : bulksketch.decode.roots.Roots) (degree : Usize) :
    (if roots.v3 then preferred RootSetup.gf64Dictionary degree else .ok false) =
      .ok (roots.v3 && decide (3 ≤ degree.val ∧ degree.val ≤ 18)) := by
  cases roots.v3
  · simp only [Bool.false_eq_true, ite_false, Bool.false_and]
  · simp only [ite_true, Bool.true_and, native_preferred_refines.2 degree]


end BulksketchBridge.AffinePreferred
