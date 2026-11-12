import BulksketchBridge.RootDivideStages
import BulksketchBridge.RootDivideArithmetic
import BulksketchBridge.WorkSchedule
import BulksketchBridge.BmPrice

namespace BulksketchBridge.RootDivide

open Aeneas.Std Aeneas.Std.RootDivideRuntime RootDivideArithmetic WorkSchedule
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch
open bulksketch.decode.work bulksketch.types
open core.result.Result.Insts

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private theorem divide_price (degree : Usize) :
    WorkScheduleV1.cost (.Divide degree) = .ok (divideCost degree) := by
  obtain ⟨word, numberNormal, wordValue⟩ := number_refines degree
  have oneValue : (1#u64).val = 1 := rfl
  have fourValue : (4#u64).val = 4 := rfl
  have extraValue : (128#u64).val = 128 := rfl
  simp only [WorkScheduleV1.cost, divideCost, numberNormal, bind_ok, CoreOpsTry.branch,
    BmPrice.add_refines, wordValue, oneValue]
  change Aeneas.Std.bind (add word 1#u64) _ = _
  rw [BmPrice.add_refines word 1#u64, wordValue, oneValue, bind_ok]
  cases checkedCost (degree.val + 1) with
  | Err error =>
    simp only [bind_ok, CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
    exact bind_ok _ _
  | Ok width =>
    simp only [bind_ok, CoreOpsTry.branch]
    change Aeneas.Std.bind (mul width width) _ = _
    rw [mul_refines width width, bind_ok]
    cases checkedCost (width.val * width.val) with
    | Err error =>
      simp only [bind_ok, CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
      exact bind_ok _ _
    | Ok square =>
      simp only [bind_ok, CoreOpsTry.branch]
      change Aeneas.Std.bind (mul 4#u64 square) _ = _
      rw [mul_refines 4#u64 square, fourValue, bind_ok]
      cases checkedCost (4 * square.val) with
      | Err error =>
        simp only [bind_ok, CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
        exact bind_ok _ _
      | Ok work =>
        simp only [bind_ok, CoreOpsTry.branch]
        change Aeneas.Std.bind (add work 128#u64) _ = _
        rw [BmPrice.add_refines work 128#u64, extraValue, bind_ok]
        cases checkedCost (work.val + 128) <;> simp [CoreOpsTry_traitFromResidualResult.from_residual]

private theorem assembly_price (degree : Usize) :
    WorkScheduleV1.cost (.SplitAssembly degree) = .ok (assemblyCost degree) := by
  obtain ⟨word, numberNormal, wordValue⟩ := number_refines degree
  have oneValue : (1#u64).val = 1 := rfl
  have fourValue : (4#u64).val = 4 := rfl
  simp only [WorkScheduleV1.cost, assemblyCost, numberNormal, bind_ok, CoreOpsTry.branch,
    BmPrice.add_refines, wordValue, oneValue]
  change Aeneas.Std.bind (add word 1#u64) _ = _
  rw [BmPrice.add_refines word 1#u64, wordValue, oneValue, bind_ok]
  cases checkedCost (degree.val + 1) with
  | Err error =>
    simp only [bind_ok, CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
    exact bind_ok _ _
  | Ok width =>
    simp only [bind_ok, CoreOpsTry.branch]
    change Aeneas.Std.bind (mul 4#u64 width) _ = _
    rw [mul_refines 4#u64 width, fourValue, bind_ok]
    cases checkedCost (4 * width.val) <;> simp [CoreOpsTry_traitFromResidualResult.from_residual]

private theorem committed_refines (exactDivision : ExactDivide) {F K : Type}
    (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F)
    (roots : Roots) (buffers : FactorWork) (factors : Slice U64) (stack : Slice FactorFrame)
    (meter paid finalMeter : WorkMeter) (length start stop : Usize)
    (quotient remainder : Slice U64) (raw : Slice RawProduct)
    (ready : DivideReady roots buffers) (commit : CommitReady roots buffers factors stack quotient length start stop)
    (charged : charge meter (.Divide roots.degree) = .ok (.Ok (), paid))
    (call : reached exactDivision field kernels roots buffers (some length) quotient remainder raw)
    (assembly : charge paid (.SplitAssembly roots.degree) = .ok (.Ok (), finalMeter))
    (startOk : Usize.checked_mul roots.pending roots.stride = some start)
    (endOk : Usize.checked_add start length = some stop) :
    Roots.divide exactDivision field kernels roots buffers factors stack meter =
      .ok (committed roots buffers factors stack finalMeter length start quotient remainder raw) := by
  have endpoint := Usize.checked_add_bv_spec start length
  simp only [endOk] at endpoint
  have stackRoom : stack.length ≤ Usize.max := stack.length_ineq
  have pendingRoom : roots.pending.val + 1 ≤ Usize.max := by
    have := commit.slotRoom
    omega
  obtain ⟨pending, pendingOk, pendingVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := roots.pending) (y := 1#usize) (by exact pendingRoom))
  have pendingWord : pending = ClosedLeafAdvance.usizeWord (roots.pending.val + 1) :=
    UScalar.eq_of_val_eq (pendingVal.trans (ClosedLeafAdvance.word_val _ pendingRoom).symm)
  obtain ⟨direction, directionOk, directionVal⟩ := RawMulTable.normal_of_spec _ _
    (U32.add_spec (x := roots.direction) (y := 1#u32) (by exact commit.directionRoom))
  have dirRoom : roots.direction.val + 1 < 2 ^ 32 := by
    have bound := commit.directionRoom
    rw [U32.max_eq] at bound
    omega
  have directionExact : direction = directionWord roots := by
    apply UScalar.eq_of_val_eq
    rw [directionVal]
    change roots.direction.val + 1 = (BitVec.ofNat 32 (roots.direction.val + 1)).toNat
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt dirRoom]
  cases affine : roots.affine with
  | false =>
    simpa only [committed, affine, Bool.false_eq_true, ite_false, directionExact, pendingWord] using
      commit_nonaffine exactDivision field kernels roots buffers factors stack meter paid finalMeter
        length start stop pending (UScalar.cast .U64 start) (UScalar.cast .U64 length) direction
        quotient remainder raw ready.workRoom ready.gcdRoom charged call assembly startOk endOk endpoint.2.1
        commit.factorRoom commit.quotientRoom commit.slotRoom commit.modulusRoom
        (offset_word start) (offset_word length) directionOk pendingOk affine
  | true =>
    obtain ⟨basis, basisPresent⟩ := commit.affineBasis affine
    obtain ⟨rank, rankOk, rankVal, _⟩ := RawMulTable.normal_of_spec _ _
      (Usize.sub_spec (x := roots.affine_rank) (y := 1#usize) (by
        change 1 ≤ roots.affine_rank.val
        exact (commit.affineRank affine).1))
    have rankValue : rank.val = roots.affine_rank.val - 1 := rankVal
    have rankRoom : rank.val < 64 := by
      have := (commit.affineRank affine).2
      omega
    have rankFits : roots.affine_rank.val - 1 ≤ Usize.max := by
      have bound : roots.affine_rank.val ≤ Usize.max := by scalar_tac
      omega
    have rankWord : rank = ClosedLeafAdvance.usizeWord (roots.affine_rank.val - 1) :=
      UScalar.eq_of_val_eq (rankValue.trans (ClosedLeafAdvance.word_val _ rankFits).symm)
    obtain ⟨basisWord, basisRead, basisValue⟩ := RawMulTable.normal_of_spec _ _
      (Array.index_usize_spec basis rank (by simpa using rankRoom))
    have basisExact : basisWord = basis[rank.val]! := by
      rw [basisValue, Array.getElem!_Nat_eq]
      exact List.Inhabited_getElem_eq_getElem! _ _ (by simpa using rankRoom)
    obtain ⟨basePositive, baseRoom⟩ := commit.affineBase affine
    have factorsMax : factors.length ≤ Usize.max := factors.length_ineq
    have sumRoom : start.val + roots.stride.val ≤ Usize.max := by omega
    obtain ⟨baseSum, sumOk, sumVal⟩ := RawMulTable.normal_of_spec _ _
      (Usize.add_spec (x := start) (y := roots.stride) sumRoom)
    obtain ⟨baseIndex, indexOk, indexVal, _⟩ := RawMulTable.normal_of_spec _ _
      (Usize.sub_spec (x := baseSum) (y := 1#usize) (by change 1 ≤ baseSum.val; omega))
    have indexValue : baseIndex.val = start.val + roots.stride.val - 1 := by
      rw [indexVal, sumVal]
      rfl
    have baseExact : baseIndex = ClosedLeafAdvance.usizeWord (start.val + roots.stride.val - 1) :=
      UScalar.eq_of_val_eq (indexValue.trans (ClosedLeafAdvance.word_val _ (by omega)).symm)
    simpa only [committed, affine, ite_true, directionExact, pendingWord, ← rankWord, ← baseExact,
      basisPresent, Option.map_some, Option.getD_some, basisExact] using
      commit_affine exactDivision field kernels roots buffers factors stack meter paid finalMeter
        length start stop pending rank baseSum baseIndex basis basisWord (UScalar.cast .U64 start)
        (UScalar.cast .U64 length) direction quotient remainder raw ready.workRoom ready.gcdRoom
        charged call assembly startOk endOk endpoint.2.1 commit.factorRoom commit.quotientRoom commit.slotRoom
        commit.modulusRoom (offset_word start) (offset_word length) directionOk pendingOk affine
        rankOk basisPresent basisRead sumOk indexOk (by omega)

theorem divide_refines : ActualRootDivide := by
  intro exactDivision F K field kernels roots buffers factors stack meter ready returns admitted
  have chargeOne : charge meter (.Divide roots.degree) =
      .ok (StageCharge.chargeResult meter (divideCost roots.degree)) := by
    rw [ClosedLeafAdvance.charge_refines]
    simp only [divide_price, bind_ok]
  unfold expected
  cases firstEq : StageCharge.chargeResult meter (divideCost roots.degree) with
  | mk first paid =>
    rw [firstEq] at chargeOne
    cases first with
    | Err error =>
      exact first_charge_failure exactDivision field kernels roots buffers factors stack meter paid error chargeOne
    | Ok unit =>
      cases unit
      obtain ⟨candidate, quotient, remainder, raw, call⟩ := returns
      have evaluated := call
      unfold reached at evaluated
      simp only [evaluated, bind_ok]
      cases candidate with
      | none =>
        exact nonexact_failure exactDivision field kernels roots buffers factors stack meter paid
          quotient remainder raw ready.workRoom ready.gcdRoom chargeOne call
      | some length =>
        have chargeTwo : charge paid (.SplitAssembly roots.degree) =
            .ok (StageCharge.chargeResult paid (assemblyCost roots.degree)) := by
          rw [ClosedLeafAdvance.charge_refines]
          simp only [assembly_price, bind_ok]
        cases secondEq : StageCharge.chargeResult paid (assemblyCost roots.degree) with
        | mk second finalMeter =>
          rw [secondEq] at chargeTwo
          cases second with
          | Err error =>
            exact assembly_charge_failure exactDivision field kernels roots buffers factors stack
              meter paid finalMeter length quotient remainder raw error ready.workRoom ready.gcdRoom chargeOne call chargeTwo
          | Ok unit =>
            cases unit
            cases startOk : Usize.checked_mul roots.pending roots.stride with
            | none =>
              exact offset_overflow exactDivision field kernels roots buffers factors stack
                meter paid finalMeter length quotient remainder raw ready.workRoom ready.gcdRoom
                chargeOne call chargeTwo startOk
            | some start =>
              dsimp! only
              cases endOk : Usize.checked_add start length with
              | none =>
                exact endpoint_overflow exactDivision field kernels roots buffers factors stack
                  meter paid finalMeter length start quotient remainder raw ready.workRoom ready.gcdRoom
                  chargeOne call chargeTwo startOk endOk
              | some stop =>
                exact committed_refines exactDivision field kernels roots buffers factors stack
                  meter paid finalMeter length start stop quotient remainder raw ready
                  (admitted length quotient remainder raw start stop call startOk endOk)
                  chargeOne call chargeTwo startOk endOk

end BulksketchBridge.RootDivide
