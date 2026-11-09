import Arithmetic.AffineSelectorGenerated
import BulksketchBridge.RawMulTable

namespace BulksketchBridge.AffineSelector

open Aeneas Aeneas.Std Result Error WP
open bulksketch.decode.affine

set_option maxHeartbeats 1500000

def word (n : Nat) : U64 := ⟨BitVec.ofNat 64 n⟩

theorem word_val (n : Nat) (fits : n ≤ U64.max) : (word n).val = n := by
  rw [U64.max_eq] at fits
  change n % (2 ^ 64) = n
  exact Nat.mod_eq_of_lt (by omega)

private theorem word_of_val (u : U64) : word u.val = u := by
  apply UScalar.eq_of_val_eq
  apply word_val
  simpa only [U64.max_eq] using u.le_max

def checked (n : Nat) : Result U64 :=
  if n ≤ U64.max then .ok (word n) else .fail integerOverflow

private theorem bounds_equiv (n : Nat) : UScalar.check_bounds .U64 n ↔ n ≤ U64.max := by
  rw [UScalar.check_bounds_eq_inBounds, UScalar.inBounds, U64.max_eq]
  change n < 18446744073709551616 ↔ n ≤ 18446744073709551615
  omega

private theorem try_word (n : Nat) : UScalar.tryMk .U64 n = checked n := by
  rw [UScalar.tryMk, UScalar.tryMkOpt, checked]
  by_cases fits : n ≤ U64.max
  · rw [dite_eq_left ((bounds_equiv n).mpr fits), ite_eq_left fits]
    apply congrArg Result.ok
    apply UScalar.eq_of_val_eq
    rw [word_val _ fits]
    exact UScalar.ofNatCore_val_eq _
  · rw [dite_eq_right (fun h => fits ((bounds_equiv n).mp h)), ite_eq_right fits]
    rfl

private theorem add_word (a b : U64) : (a + b : Result U64) = checked (a.val + b.val) :=
  try_word _

private theorem mul_word (a b : U64) : (a * b : Result U64) = checked (a.val * b.val) :=
  try_word _

private theorem product_option (a b : U64) : U64.checked_mul a b =
    if a.val * b.val ≤ U64.max then some (word (a.val * b.val)) else none := by
  have behavior := U64.checked_mul_bv_spec a b
  cases branch : U64.checked_mul a b with
  | none =>
    simp only [branch] at behavior
    rw [ite_eq_right (Nat.not_le_of_gt behavior)]
  | some result =>
    simp only [branch] at behavior
    rw [ite_eq_left behavior.1, ← behavior.2.1, word_of_val]

private theorem div_ceil_eight (x : U64) :
    core.num.U64.div_ceil x 8#u64 = .ok (word ((x.val + 7) / 8)) := by
  obtain ⟨q, quotient, qval⟩ := RawMulTable.normal_of_spec _ _
    (U64.div_spec x (y := 8#u64) (by decide))
  obtain ⟨r, remainder, rval⟩ := RawMulTable.normal_of_spec _ _
    (UScalar.rem_spec x (y := 8#u64) (by decide))
  change q.val = x.val / 8 at qval
  change r.val = x.val % 8 at rval
  have max : x.val ≤ U64.max := by simpa only [U64.max_eq] using x.le_max
  have increment : x.val / 8 + 1 ≤ U64.max := by
    rw [U64.max_eq] at max ⊢
    omega
  simp only [core.num.U64.div_ceil, quotient, remainder, bind_ok,
    UScalar.lt_equiv, rval, show (0#u64).val = 0 from rfl]
  split <;> rename_i nonzero
  · rw [add_word, qval, show (1#u64).val = 1 from rfl, checked, ite_eq_left increment]
    congr 2
    omega
  · rw [← word_of_val q, qval]
    congr 2
    omega

def squareCount (degree : Nat) : Nat :=
  3 * degree + (2 * (degree / 2)) * ((degree + 7) / 8)

def ActualSquareProducts : Prop :=
  ∀ degree : U64, square_products degree = checked (squareCount degree.val)

theorem square_products_refines : ActualSquareProducts := by
  intro degree
  obtain ⟨half, halfOk, halfVal⟩ := RawMulTable.normal_of_spec _ _
    (U64.div_spec degree (y := 2#u64) (by decide))
  change half.val = degree.val / 2 at halfVal
  have max : degree.val ≤ U64.max := by simpa only [U64.max_eq] using degree.le_max
  have twice : 2 * (degree.val / 2) ≤ U64.max := by omega
  have block : (degree.val + 7) / 8 ≤ U64.max := by rw [U64.max_eq] at max ⊢; omega
  simp only [square_products, mul_word 3#u64 degree, show (3#u64).val = 3 from rfl]
  by_cases linear : 3 * degree.val ≤ U64.max
  · simp only [checked, linear, ite_true, bind_ok, halfOk,
      show (2#u64).val = 2 from rfl, halfVal, twice, div_ceil_eight,
      mul_word, word_val _ twice, word_val _ block]
    by_cases vector : 2 * (degree.val / 2) * ((degree.val + 7) / 8) ≤ U64.max
    · simp only [vector, ite_true, bind_ok, add_word, checked, word_val _ linear,
        word_val _ vector, squareCount]
      rfl
    · have total : ¬ squareCount degree.val ≤ U64.max := by unfold squareCount; omega
      simp only [vector, ite_false, bind_fail, total]
  · have total : ¬ squareCount degree.val ≤ U64.max := by unfold squareCount; omega
    simp only [checked, linear, ite_false, bind_fail, total]

def enumerationModel (degree rank : Nat) : Result Bool :=
  let shift := rank % (2 ^ 32)
  if shift < 64 then
    let blocks := (2 ^ shift + 7) / 8
    do
      let lanes ← checked (6 * degree)
      let price := blocks * lanes.val
      if price ≤ U64.max then
        let squares ← checked (squareCount degree)
        let rankPrice ← checked (rank * squares.val)
        let extra ← checked (85 * degree)
        let splitPrice ← checked (rankPrice.val + extra.val)
        .ok (decide (price ≤ splitPrice.val))
      else .ok false
  else .ok false

private theorem usize_to_word (x : Usize) : (UScalar.cast .U64 x).val = x.val := by
  rw [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  exact lt_of_lt_of_le x.hBounds (Nat.pow_le_pow_right (by decide) System.Platform.numBits_le)

private theorem shift_one (rank : U32) (small : rank.val < 64) :
    (⟨(1#u64).bv <<< rank.val⟩ : U64) = word (2 ^ rank.val) := by
  apply UScalar.eq_of_val_eq
  rw [word_val _ (by
    rw [U64.max_eq]
    have fit := Nat.pow_lt_pow_right (a := 2) (by decide) small
    omega)]
  change ((1#u64).bv <<< rank.val).toNat = _
  rw [BitVec.toNat_shiftLeft, show (1#u64).bv.toNat = 1 from rfl, Nat.shiftLeft_eq, Nat.one_mul]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) small)

/-- The checked model covers every input, including u32 narrowing of the
shift amount, checked enumeration overflow, and the ordinary arithmetic
failures on out-of-domain input. -/
def ActualEnumeratePreferred : Prop :=
  ∀ degree rank : Usize, enumerate_preferred degree rank = enumerationModel degree.val rank.val

theorem enumerate_preferred_refines : ActualEnumeratePreferred := by
  intro degree rank
  unfold enumerate_preferred enumerationModel
  simp only [lift, bind_ok]
  set narrow := (UScalar.cast .U32 rank) with narrowEq
  have narrowVal : narrow.val = rank.val % (2 ^ 32) := by
    rw [narrowEq]
    exact UScalar.cast_val_eq .U32 rank
  have degreeVal := usize_to_word degree
  have rankVal := usize_to_word rank
  by_cases small : narrow.val < 64
  · have pointBound : 2 ^ narrow.val ≤ U64.max := by
      rw [U64.max_eq]
      have fit := Nat.pow_lt_pow_right (a := 2) (by decide) small
      omega
    have blockBound : (2 ^ narrow.val + 7) / 8 ≤ U64.max := by
      rw [U64.max_eq] at pointBound ⊢
      omega
    simp only [core.num.U64.checked_shl, small, ite_true, shift_one narrow small, bind_ok,
      div_ceil_eight, word_val _ pointBound, mul_word 6#u64,
      show (6#u64).val = 6 from rfl, degreeVal, ← narrowVal]
    by_cases lanesFit : 6 * degree.val ≤ U64.max
    · simp only [checked, lanesFit, ite_true, bind_ok, product_option, word_val _ blockBound]
      let price := (2 ^ narrow.val + 7) / 8 * (word (6 * degree.val)).val
      by_cases fits : price ≤ U64.max
      · have good : (2 ^ narrow.val + 7) / 8 * (word (6 * degree.val)).val ≤ U64.max := fits
        have eightyFour : (3#u64 * 28#u64 : Result U64) = .ok (84#u64) := by
          rw [mul_word]
          change checked 84 = _
          rw [checked, ite_eq_left (by rw [U64.max_eq]; decide)]
          rfl
        have addOne : (84#u64 + 1#u64 : Result U64) = .ok (85#u64) := by
          rw [add_word]
          change checked 85 = _
          rw [checked, ite_eq_left (by rw [U64.max_eq]; decide)]
          rfl
        have square := square_products_refines (UScalar.cast .U64 degree)
        simp only [good, ite_true, eightyFour, bind_ok, square, degreeVal]
        simp only [addOne, bind_ok]
        simp only [mul_word, rankVal, show (85#u64).val = 85 from rfl,
          add_word, UScalar.le_equiv, word_val _ good, degreeVal]
        rfl
      · have bad : ¬ (2 ^ narrow.val + 7) / 8 * (word (6 * degree.val)).val ≤ U64.max := fits
        simp only [bad, ite_false]
    · simp only [checked, lanesFit, ite_false, bind_fail]
  · simp only [core.num.U64.checked_shl, small, ite_false, bind_ok, ← narrowVal]

#print axioms square_products_refines
#print axioms enumerate_preferred_refines

end BulksketchBridge.AffineSelector
