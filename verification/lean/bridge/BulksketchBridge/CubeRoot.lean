import BulksketchBridge.CubeRootSpec
import BulksketchBridge.Algebra.WordNative
import BulksketchBridge.Algebra.InversePower
import Mathlib.Tactic.IntervalCases

namespace BulksketchBridge.CubeRoot

open Aeneas Aeneas.Std Algebra.Gf64 bulksketch.backend.contract bulksketch.decode.deg34

private def chainExponent : Nat → Nat
  | 0 => 1
  | count + 1 => chainExponent count * 64 + 49

private def rangeAt (count : Nat) : core.ops.range.Range I32 :=
  { start := ⟨BitVec.ofNat 32 count⟩, «end» := 10#i32 }

private theorem range_start (count : Nat) (bounded : count ≤ 10) :
    (rangeAt count).start.val = (count : Int) := by
  interval_cases count <;> rfl

private theorem next_step (count : Nat) (active : count < 10) :
    core.iter.range.IteratorRange.next core.iter.range.StepI32 (rangeAt count) =
      Result.ok (some (rangeAt count).start, rangeAt (count + 1)) := by
  have startVal := range_start count (by omega)
  have nextVal := range_start (count + 1) (by omega)
  have endVal : (rangeAt count).end.val = 10 := rfl
  have one : (1#usize).val = 1 := by simp
  have cmp : core.cmp.impls.PartialOrdI32.lt (rangeAt count).start (rangeAt count).end = true := by
    change decide ((rangeAt count).start.val < (rangeAt count).end.val) = _
    rw [startVal, endVal]
    simp only [show (count : Int) < 10 by omega, decide_true]
  have step : core.iter.range.IScalarStep.forward_checked (rangeAt count).start 1#usize =
      Result.ok (some (rangeAt (count + 1)).start) := by
    have fits : (rangeAt count).start.val + (1#usize).val ≤ IScalar.max .I32 := by
      have max32 : IScalar.max .I32 = 2147483647 := by simp [I32.max_eq]
      rw [startVal, one, max32]
      omega
    unfold core.iter.range.IScalarStep.forward_checked
    rw [dite_eq_left fits]
    apply congrArg (fun word : I32 => Result.ok (some word))
    apply IScalar.eq_of_val_eq
    rw [IScalar.ofInt_val_eq, startVal, nextVal, one]
    omega
  simp only [core.iter.range.IteratorRange.next, core.iter.range.StepI32,
    core.iter.range.IScalarStep, core.cmp.PartialOrdI32, core.clone.CloneI32,
    cmp, bind_ok, ite_true, core.clone.impls.CloneI32.clone, step]
  rfl

private theorem next_done : core.iter.range.IteratorRange.next core.iter.range.StepI32 (rangeAt 10) =
    Result.ok (none, rangeAt 10) := by
  simp [rangeAt, core.iter.range.IteratorRange.next, core.iter.range.StepI32,
    core.iter.range.IScalarStep, core.cmp.PartialOrdI32, core.cmp.impls.PartialOrdI32.lt, IScalar.val]

private theorem mul_field {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : CorrectArithmetic kernels) (a b : U64) :
    ∃ output : U64, kernels.ArithmeticInst.mul a b = Result.ok output ∧
      toField output.bv = toField a.bv * toField b.bv := by
  rw [arithmetic.1]
  exact native_mul_is_field a b

private theorem square_field {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : CorrectArithmetic kernels) (a : U64) :
    ∃ output : U64, kernels.ArithmeticInst.square a = Result.ok output ∧
      toField output.bv = toField a.bv ^ 2 := by
  rw [arithmetic.2.1]
  exact native_square_is_field a

private theorem frobenius_field {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : CorrectArithmetic kernels) (a : U64) (power : U32) :
    ∃ output : U64, kernels.ArithmeticInst.frobenius a power = Result.ok output ∧
      toField output.bv = toField a.bv ^ (2 ^ power.val) := by
  rw [arithmetic.2.2]
  exact native_frobenius_is_field a power

private theorem chain_refines {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : CorrectArithmetic kernels) (input t49 : U64)
    (t49Meaning : toField t49.bv = toField input.bv ^ 49)
    (count : Nat) (bounded : count ≤ 10) (current : U64)
    (currentMeaning : toField current.bv = toField input.bv ^ chainExponent count) :
    ∃ output : U64,
      cube_root_loop fieldDictionary kernels (rangeAt count) t49 current = Result.ok output ∧
      toField output.bv = toField input.bv ^ chainExponent 10 := by
  suffices ∀ remaining count, count ≤ 10 → 10 - count = remaining → ∀ current : U64,
      toField current.bv = toField input.bv ^ chainExponent count →
      ∃ output : U64,
        cube_root_loop fieldDictionary kernels (rangeAt count) t49 current = Result.ok output ∧
        toField output.bv = toField input.bv ^ chainExponent 10 from
    this (10 - count) count bounded rfl current currentMeaning
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
    intro count bounded remainingEq current currentMeaning
    by_cases active : count < 10
    · obtain ⟨frob, normalFrob, frobMeaning⟩ := frobenius_field kernels arithmetic current (6#u32)
      obtain ⟨next, normalMul, mulMeaning⟩ := mul_field kernels arithmetic frob t49
      have meaning : toField next.bv = toField input.bv ^ chainExponent (count + 1) := by
        rw [mulMeaning, frobMeaning, currentMeaning, t49Meaning]
        change (toField input.bv ^ chainExponent count) ^ 64 * toField input.bv ^ 49 = _
        rw [← pow_mul, ← pow_add]
        rfl
      have step : cube_root_loop.body fieldDictionary kernels t49 (rangeAt count) current =
          Result.ok (ControlFlow.cont (rangeAt (count + 1), next)) := by
        simp only [cube_root_loop.body, next_step count active, bind_ok]
        dsimp! only
        simp only [normalFrob, normalMul, bind_ok]
      obtain ⟨output, normal, fieldMeaning⟩ := ih (10 - (count + 1)) (by omega) (count + 1)
        (by omega) rfl next meaning
      refine ⟨output, ?_, fieldMeaning⟩
      unfold cube_root_loop loop
      dsimp only
      rw [step]
      simpa only [cube_root_loop, bind_ok] using normal
    · have final : count = 10 := by omega
      subst count
      refine ⟨current, ?_, currentMeaning⟩
      unfold cube_root_loop loop
      dsimp only
      simp only [cube_root_loop.body, next_done, bind_ok]
      dsimp! only
      simp only [bind_ok]

private theorem word_nonzero (word : U64) (nonzero : word ≠ 0#u64) : toField word.bv ≠ 0 := by
  intro zero
  apply nonzero
  apply U64.bv_eq_imp_eq
  apply toField_injective
  exact zero.trans toField_zero.symm

private theorem candidate_of_cube (input : Field) (root : Field) (nonzero : root ≠ 0)
    (isCube : root ^ 3 = input) : input ^ cubeExponent ≠ 0 ∧ (input ^ cubeExponent) ^ 3 = input := by
  subst input
  refine ⟨pow_ne_zero _ (pow_ne_zero _ nonzero), ?_⟩
  rw [← pow_mul, ← pow_mul, show 3 * (cubeExponent * 3) = 2 ^ 64 + 2 by decide +kernel,
    pow_add, field_power_period, pow_succ root 2, mul_comm]

/-- The actual ten-step chain, its final multiplication, and the original
nonzero and cubing guards give a complete cube-root decision. -/
theorem cube_root_refines : ActualCubeRootComplete := by
  intro K kernels input arithmetic
  obtain ⟨t16, normal16, meaning16⟩ := frobenius_field kernels arithmetic input (4#u32)
  obtain ⟨t32, normal32, meaning32⟩ := square_field kernels arithmetic t16
  obtain ⟨t48, normal48, meaning48⟩ := mul_field kernels arithmetic t32 t16
  obtain ⟨t49, normal49, meaning49⟩ := mul_field kernels arithmetic t48 input
  have exact49 : toField t49.bv = toField input.bv ^ 49 := by
    rw [meaning49, meaning48, meaning32, meaning16]
    change (toField input.bv ^ 16) ^ 2 * toField input.bv ^ 16 * toField input.bv = _
    rw [← pow_mul, ← pow_add, ← pow_succ]
  obtain ⟨last, chainNormal, chainMeaning⟩ := chain_refines kernels arithmetic input t49 exact49
    0 (by decide) input (by simp [chainExponent])
  obtain ⟨candidate, normalCandidate, candidateMeaning⟩ := mul_field kernels arithmetic last input
  have exactCandidate : toField candidate.bv = toField input.bv ^ cubeExponent := by
    rw [candidateMeaning, chainMeaning, ← pow_succ, show chainExponent 10 + 1 = cubeExponent by decide +kernel]
  have exhausted (rejected : ¬ (toField candidate.bv ≠ 0 ∧
      toField candidate.bv ^ 3 = toField input.bv)) :
      ¬∃ root : Field, root ≠ 0 ∧ root ^ 3 = toField input.bv := by
    rintro ⟨root, nonzero, cube⟩
    apply rejected
    rw [exactCandidate]
    exact candidate_of_cube _ root nonzero cube
  have sourceChain : cube_root_loop fieldDictionary kernels
      { start := 0#i32, «end» := 10#i32 } t49 input = Result.ok last := chainNormal
  by_cases zero : candidate = 0#u64
  · refine ⟨none, ?_, exhausted (fun valid => valid.1 (by rw [zero]; exact toField_zero))⟩
    simp [cube_root, normal16, normal32, normal48, normal49, sourceChain,
      normalCandidate, zero, CubeRootRuntime.thenSome]
  · obtain ⟨squared, squareNormal, squareMeaning⟩ := square_field kernels arithmetic candidate
    obtain ⟨cubed, cubeNormal, cubeMeaning⟩ := mul_field kernels arithmetic squared candidate
    have cubeField : toField cubed.bv = toField candidate.bv ^ 3 := by
      rw [cubeMeaning, squareMeaning, pow_succ _ 2]
    have nzVal : candidate.val ≠ 0 := by
      intro value
      apply zero
      apply UScalar.eq_of_val_eq
      exact value
    by_cases equal : cubed = input
    · refine ⟨some candidate, ?_, word_nonzero candidate zero, cubeField.symm.trans (congrArg
        (fun word : U64 => toField word.bv) equal), exactCandidate⟩
      simp [cube_root, normal16, normal32, normal48, normal49, sourceChain,
        normalCandidate, nzVal, squareNormal, cubeNormal, equal, CubeRootRuntime.thenSome]
    · have notCube : toField candidate.bv ^ 3 ≠ toField input.bv := by
        intro cubeEq
        apply equal
        apply U64.bv_eq_imp_eq
        exact toField_injective (cubeField.trans cubeEq)
      refine ⟨none, ?_, exhausted (fun valid => notCube valid.2)⟩
      simp [cube_root, normal16, normal32, normal48, normal49, sourceChain,
        normalCandidate, nzVal, squareNormal, cubeNormal, equal, CubeRootRuntime.thenSome]

end BulksketchBridge.CubeRoot
