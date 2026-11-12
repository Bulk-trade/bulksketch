import BulksketchBridge.RootSetup
import BulksketchBridge.RawMulTable

namespace BulksketchBridge.AffinePreferred

open Aeneas Aeneas.Std Result ControlFlow
open bulksketch.decode.affine

private theorem cast_bits :
    UScalar.cast .Usize (64#u32) = 64#usize := by
  apply UScalar.eq_of_val_eq
  rw [UScalar.cast_val_eq]
  have bits : 64 < 2 ^ UScalarTy.Usize.numBits := by
    change 64 < 2 ^ System.Platform.numBits
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide
  have val : (64#u32).val = 64 := rfl
  rw [val, Nat.mod_eq_of_lt bits]
  exact (Usize.ofNatCore_val_eq _).symm

/-- Interpret the original mask lookup once the constant's exact value is available. -/
def ActualPreferredUnderMask : Prop :=
  PREFERRED_MASK = .ok 524280#u64 →
  ∀ degree : Usize, preferred RootSetup.gf64Dictionary degree =
    .ok (decide (3 ≤ degree.val ∧ degree.val ≤ 18))

private theorem low_mask :
    ∀ degree : Fin 64, ((0x7fff8#64 &&& (1#64 <<< degree.val)) != 0#64) =
      decide (3 ≤ degree.val ∧ degree.val ≤ 18) := by decide

theorem preferred_under_mask : ActualPreferredUnderMask := by
  intro mask degree
  have sixtyFour : (64#usize).val = 64 := Usize.ofNatCore_val_eq _
  have castField :
      UScalar.cast .Usize bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS = 64#usize :=
    by rw [bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS]; exact cast_bits
  unfold preferred
  simp only [bind_ok, lift, castField, UScalar.lt_equiv, sixtyFour]
  by_cases small : degree.val < 64
  · have shift : (1#u64 <<< degree : Result U64) = .ok ⟨(1#64 <<< degree.val)⟩ := by
      change (if degree.val < 64 then ok (⟨(1#64 <<< degree.val)⟩ : U64) else fail .integerOverflow) = _
      rw [ite_eq_left small]
    simp only [small, ite_true, shift, bind_ok, mask]
    congr 1
    change ((524280#u64 &&& ⟨(1#64 <<< degree.val)⟩) != 0#u64) = _
    exact low_mask ⟨degree.val, small⟩
  · simp only [small, ite_false]
    congr 1
    symm
    exact decide_eq_false (by omega)

/-- Number of the predictor's initial unit columns for a nontrivial degree. -/
def unitColumns (degree : Nat) : Nat := 2 + Nat.log 2 (degree - 1)

/-- Exact nested sum from the source's checked Gaussian price loops. -/
def gaussianPrice (degree : Nat) : Nat :=
  ((List.range (degree + 1 - unitColumns degree)).map fun offset =>
    let column := unitColumns degree + offset
    ((List.range column).map fun pivot =>
      2 * ((degree - pivot + 7) / 8 + (column + 8) / 8)).sum).sum

def predicts (degree : Nat) : Bool :=
  let unit := unitColumns degree
  let affine := gaussianPrice degree + 3 * degree * (degree + 1) + 28 * (degree - unit) +
    16 * degree + 6 * degree * (degree - 1)
  let squares := 3 * degree + 2 * (degree / 2) * ((degree + 7) / 8)
  decide (affine < (64 - degree) * squares)

/-- Exact result of the source predictor's scalar arithmetic and two loops. -/
def ActualPredictorOnMaskDomain : Prop :=
  ∀ degree : Usize, 3 ≤ degree.val → degree.val < 64 →
    predicted_affine degree = .ok (predicts degree.val)

private def maskStep (degree : Nat) (mask : U64) : U64 :=
  if predicts degree then mask ||| ⟨(1#64 <<< degree)⟩ else mask

private def maskSuffix : Nat → Nat → U64 → U64
  | 0, _, mask => mask
  | fuel + 1, degree, mask => maskSuffix fuel (degree + 1) (maskStep degree mask)

private theorem mask_suffix_native (predictor : ActualPredictorOnMaskDomain)
    (fuel : Nat) (degree : Usize) (mask : U64) (lower : 3 ≤ degree.val)
    (remaining : degree.val + fuel = 64) :
    PREFERRED_MASK_loop degree mask = .ok (maskSuffix fuel degree.val mask) := by
  have sixtyFour : (64#usize).val = 64 := Usize.ofNatCore_val_eq _
  induction fuel generalizing degree mask with
  | zero =>
    have stop : ¬ degree.val < 64 := by omega
    rw [PREFERRED_MASK_loop, loop]
    simp only [PREFERRED_MASK_loop.body, UScalar.lt_equiv, sixtyFour, stop, ite_false, bind_ok,
      maskSuffix]
  | succ fuel ih =>
    have active : degree.val < 64 := by omega
    have one : (1#usize).val = 1 := Usize.ofNatCore_val_eq _
    have fits : degree.val + (1#usize).val ≤ Usize.max := by
      have ample : 64 ≤ Usize.max := by
        rcases Usize.bounds_eq with h | h
        · rw [h, U32.max_eq]; decide
        · rw [h, U64.max_eq]; decide
      omega
    obtain ⟨next, add, nextVal⟩ := RawMulTable.normal_of_spec _ _
      (Usize.add_spec (x := degree) (y := 1#usize) fits)
    change next.val = degree.val + (1#usize).val at nextVal
    rw [one] at nextVal
    have shift : (1#u64 <<< degree : Result U64) = .ok ⟨(1#64 <<< degree.val)⟩ := by
      change (if degree.val < 64 then ok (⟨(1#64 <<< degree.val)⟩ : U64)
        else fail .integerOverflow) = _
      rw [ite_eq_left active]
    have step : PREFERRED_MASK_loop.body degree mask =
        .ok (.cont (next, maskStep degree.val mask)) := by
      simp only [PREFERRED_MASK_loop.body, UScalar.lt_equiv, sixtyFour, active, ite_true,
        predictor degree lower active, bind_ok, add, maskStep]
      cases predicts degree.val <;> simp [shift]
    rw [PREFERRED_MASK_loop, loop]
    simp only [step, bind_ok, maskSuffix]
    change PREFERRED_MASK_loop next (maskStep degree.val mask) =
      .ok (maskSuffix fuel (degree.val + 1) (maskStep degree.val mask))
    rw [ih next _ (by omega) (by omega), nextVal]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
private theorem numeric_mask : maskSuffix 61 3 0#u64 = 524280#u64 := by decide

def ActualNativePreferredUnderPredictor : Prop :=
  ActualPredictorOnMaskDomain →
    PREFERRED_MASK = .ok 524280#u64 ∧
    ∀ degree : Usize, preferred RootSetup.gf64Dictionary degree =
      .ok (decide (3 ≤ degree.val ∧ degree.val ≤ 18))

theorem native_preferred_under_predictor : ActualNativePreferredUnderPredictor := by
  intro predictor
  have three : (3#usize).val = 3 := Usize.ofNatCore_val_eq _
  have mask : PREFERRED_MASK = .ok 524280#u64 := by
    rw [PREFERRED_MASK, mask_suffix_native predictor 61 _ _ (by omega) (by omega), three, numeric_mask]
  exact ⟨mask, preferred_under_mask mask⟩


end BulksketchBridge.AffinePreferred
