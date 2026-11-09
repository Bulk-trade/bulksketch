import BulksketchBridge.NativeHonestBmDriver
import BulksketchBridge.RootTraceCharge
import BulksketchBridge.AffineSelector

namespace BulksketchBridge.PortableFrontPayment

open Aeneas.Std BmLoop BmStepControl
open bulksketch.types

theorem pay (meter : WorkMeter) (amount : U64)
    (live : meter.exhausted = false) (fits : meter.used.val + amount.val ≤ meter.limit.val) :
    ∃ paid, StageCharge.chargeResult meter (.Ok amount) = (.Ok (), paid) ∧
      paid.used.val = meter.used.val + amount.val ∧ paid.limit = meter.limit ∧ paid.exhausted = false := by
  obtain ⟨paid, ran, used, limit, active⟩ := WorkMeter.native_work_meter_paid meter amount live fits
  rw [StageCharge.meter_charge_refines] at ran
  exact ⟨paid, Result.ok_injective ran, used, limit, active⟩

theorem pay_units (meter : WorkMeter) (units : Nat)
    (live : meter.exhausted = false) (fits : meter.used.val + units ≤ meter.limit.val) :
    ∃ paid, StageCharge.chargeResult meter (WorkSchedule.checkedCost units) = (.Ok (), paid) ∧
      paid.used.val = meter.used.val + units ∧ paid.limit = meter.limit ∧ paid.exhausted = false := by
  have bound : units ≤ U64.max := by have := meter.limit.le_max; rw [U64.max_eq] at *; omega
  have eq := (WorkSchedule.checked_cost_ok_iff units (AffineSelector.word units)).mpr
    ⟨bound, AffineSelector.word_val units bound⟩
  rw [eq]
  obtain ⟨paid, ran, used, limit, active⟩ := pay meter (AffineSelector.word units) live
    (by rwa [AffineSelector.word_val units bound])
  exact ⟨paid, ran, by rwa [AffineSelector.word_val units bound] at used, limit, active⟩

/-- Rust pays one BM charge at entry and skips the charge at index zero. -/
def chargesRemaining (state : State) : Nat :=
  state.1.«end».val - max 1 state.1.start.val

private theorem paid_iteration (input : Input) (state : State)
    (active : state.1.start.val < state.1.«end».val) (live : state.2.1.exhausted = false)
    (fits : state.2.1.used.val + chargesRemaining state * input.cost.val ≤ state.2.1.limit.val) :
    ∃ paid, stepCharge state.1.start state.2.1 input.cost = (.Ok (), paid) ∧
      paid.used.val = state.2.1.used.val + (if state.1.start = 0#usize then 0 else input.cost.val) ∧
      paid.limit = state.2.1.limit ∧ paid.exhausted = false := by
  by_cases zero : state.1.start = 0#usize
  · exact ⟨state.2.1, by simp only [stepCharge, zero, ite_true],
      by simp only [zero, ite_true, Nat.add_zero], rfl, live⟩
  · have positive : 0 < state.1.start.val :=
      Nat.pos_of_ne_zero (fun h => zero (UScalar.eq_of_val_eq h))
    have enough : 1 ≤ chargesRemaining state := by
      unfold chargesRemaining
      rw [Nat.max_eq_right positive]
      omega
    have one : input.cost.val ≤ chargesRemaining state * input.cost.val :=
      Nat.le_mul_of_pos_left _ enough
    obtain ⟨paid, charged, used, limit, active⟩ := pay state.2.1 input.cost live (by omega)
    exact ⟨paid, by simpa only [stepCharge, zero, ite_false] using charged,
      by simpa only [zero, ite_false] using used, limit, active⟩

private theorem cont_meter (input : Input) (state next : State) (paid : WorkMeter)
    (active : state.1.start.val < state.1.«end».val)
    (charged : stepCharge state.1.start state.2.1 input.cost = (.Ok (), paid))
    (taken : step input state = .cont next) : next.2.1 = paid := by
  rcases state with ⟨iter, meter, connection, previous, saved, degree, previousLen, shift, previousDelta⟩
  change iter.start.val < iter.«end».val at active
  change stepCharge iter.start meter input.cost = (.Ok (), paid) at charged
  simp only [step, Nat.not_le_of_gt active, ite_false, charged] at taken
  by_cases even : iter.start.val % 2 = 0
  · simp only [even, ite_true] at taken
    by_cases zero : BmEvenStep.deltaWord connection input.syndromes degree iter.start = 0#u64
    · simp only [zero, ite_true] at taken
      cases taken
      rfl
    · simp only [zero, ite_false] at taken
      by_cases rejects : input.budget.val < BmEvenStep.nextDegree degree iter.start
      · simp only [rejects, ite_true] at taken
        cases taken
      · simp only [rejects, ite_false] at taken
        cases taken
        unfold BmAccepted.expectedAccepted
        split <;> rfl
  · simp only [even, ite_false, eq_self, ite_true] at taken
    cases taken
    rfl

theorem run_budget (input : Input) (fuel : Nat) (state last : State) (reply : BmTerminal.Return)
    (admitted : Admitted input state) (live : state.2.1.exhausted = false)
    (fits : state.2.1.used.val + chargesRemaining state * input.cost.val ≤ state.2.1.limit.val)
    (returned : run input fuel state = some (last, reply)) :
    last.2.1.exhausted = false ∧ last.2.1.limit = state.2.1.limit ∧
      last.2.1.used.val + chargesRemaining last * input.cost.val ≤
        state.2.1.used.val + chargesRemaining state * input.cost.val := by
  induction fuel generalizing state with
  | zero =>
    cases taken : step input state with
    | done result =>
      rw [run, taken] at returned
      cases returned
      exact ⟨live, rfl, le_rfl⟩
    | cont next =>
      rw [run, taken] at returned
      cases returned
  | succ fuel ih =>
    cases taken : step input state with
    | done result =>
      rw [run, taken] at returned
      cases returned
      exact ⟨live, rfl, le_rfl⟩
    | cont next =>
      have active : state.1.start.val < state.1.«end».val := by
        by_contra bad
        rcases state with ⟨iter, meter, connection, previous, saved, degree, previousLen, shift, previousDelta⟩
        simp only [step, show iter.«end».val ≤ iter.start.val from Nat.le_of_not_gt bad, ite_true] at taken
        cases taken
      obtain ⟨paid, charge, used, limit, paidLive⟩ := paid_iteration input state active live fits
      have meterEq := cont_meter input state next paid active charge taken
      obtain ⟨nextAdmitted, index, ending⟩ := advances input state next admitted taken
      have budget : next.2.1.used.val + chargesRemaining next * input.cost.val =
          state.2.1.used.val + chargesRemaining state * input.cost.val := by
        rw [meterEq, used]
        unfold chargesRemaining
        rw [index, ending]
        by_cases zero : state.1.start = 0#usize
        · simp only [zero, ite_true, Nat.add_zero]
          rfl
        · have positive : 0 < state.1.start.val :=
            Nat.pos_of_ne_zero (fun h => zero (UScalar.eq_of_val_eq h))
          simp only [zero, ite_false, Nat.max_eq_right positive, Nat.max_eq_right (Nat.succ_le_succ (Nat.zero_le _))]
          rw [show state.1.«end».val - state.1.start.val =
            1 + (state.1.«end».val - (state.1.start.val + 1)) by omega, Nat.add_mul, Nat.one_mul, Nat.add_assoc]
      rw [run, taken] at returned
      have nextFits : next.2.1.used.val + chargesRemaining next * input.cost.val ≤ next.2.1.limit.val := by
        rwa [budget, meterEq, limit]
      obtain ⟨lastLive, lastLimit, lastFits⟩ := ih next nextAdmitted (meterEq.symm ▸ paidLive) nextFits returned
      exact ⟨lastLive, lastLimit.trans (meterEq.symm ▸ limit), lastFits.trans_eq budget⟩


/-- Both the pre-loop charge and all remaining paid iterations fit. An honest
original BM locator therefore reaches its normalized successful return. -/
theorem bm_reply_paid {K : Type} (kernels : bulksketch.backend.contract.BulkKernels K bulksketch.field.Gf64)
    (raw : BmDiscrepancy.RawArithmetic kernels) (reduce : BmDiscrepancy.ReduceArithmetic kernels)
    (mul : BmMutable.NativeMul kernels) (inverse : BmTerminal.NativeInverse kernels)
    (support : Finset Algebra.Gf64.Field) (syndromes buffers difference initial : Slice U64)
    (capacity budget : Usize) (meter : WorkMeter) (reply : BmTerminal.Return)
    (nonzero : (0 : Algebra.Gf64.Field) ∉ support) (card : support.card ≤ budget.val)
    (bound : budget.val ≤ capacity.val) (room : 3 * (capacity.val + 1) ≤ buffers.length)
    (syndromeRoom : 2 * capacity.val + 1 ≤ syndromes.length)
    (reconstructed : Reconstruction.Prefix difference initial syndromes (2 * capacity.val + 1))
    (moments : BmHonestLocator.Moments support syndromes (2 * capacity.val))
    (live : meter.exhausted = false)
    (fits : meter.used.val + max 1 (2 * capacity.val) * BmPrice.bmUnits budget ≤ meter.limit.val)
    (native : bulksketch.decode.bm.locator BmEntry.fieldDictionary kernels syndromes capacity budget buffers meter = .ok reply) :
    ∃ degree, reply.1 = .Ok (.Ok degree) ∧ reply.2.2.exhausted = false ∧ reply.2.2.limit = meter.limit ∧
      reply.2.2.used.val ≤ meter.used.val + max 1 (2 * capacity.val) * BmPrice.bmUnits budget := by
  let units := BmPrice.bmUnits budget
  have one : 1 ≤ max 1 (2 * capacity.val) := Nat.le_max_left ..
  have entryCost : units ≤ max 1 (2 * capacity.val) * units := Nat.le_mul_of_pos_left _ one
  change meter.used.val + max 1 (2 * capacity.val) * units ≤ meter.limit.val at fits
  have entryRoom : meter.used.val + units ≤ meter.limit.val := by omega
  obtain ⟨paid, first, firstUsed, firstLimit, firstLive⟩ := pay_units meter units live entryRoom
  change BmEntry.pricing meter budget = (.Ok (), paid) at first
  obtain ⟨actual, runNative, honest⟩ :=
    BmHonestLocator.honest_locator_refines kernels raw reduce mul inverse support syndromes buffers
      difference initial capacity budget meter nonzero card bound room syndromeRoom reconstructed moments
  have actualEq := Result.ok_injective (runNative.symm.trans native)
  subst actual
  rcases honest with ⟨error, failedMeter, failed, _⟩ | ⟨startMeter, last, priced, returned, outcome⟩
  · rw [first] at failed
    cases failed
  · rw [first] at priced
    cases priced
    let input := BmLocator.inputs syndromes buffers capacity budget
    let start := BmLocator.initial buffers capacity budget paid
    have inputMax : syndromes.length ≤ Usize.max := syndromes.length_ineq
    have ending : start.1.«end».val = 2 * capacity.val := ClosedLeafAdvance.word_val _ (by omega)
    have remaining : chargesRemaining start = 2 * capacity.val - 1 := by
      unfold chargesRemaining
      rw [ending]
      rfl
    have costFits : units ≤ U64.max := by have := meter.limit.le_max; rw [U64.max_eq] at *; omega
    have inputPrice : input.cost.val = units := AffineSelector.word_val _ costFits
    have identity : 1 + (2 * capacity.val - 1) = max 1 (2 * capacity.val) := by omega
    have startFits : start.2.1.used.val + chargesRemaining start * input.cost.val ≤ start.2.1.limit.val := by
      change paid.used.val + chargesRemaining start * input.cost.val ≤ paid.limit.val
      rw [remaining, inputPrice, firstUsed, firstLimit]
      simpa only [← identity, Nat.add_mul, Nat.one_mul, Nat.add_assoc] using fits
    obtain ⟨lastLive, lastLimit, spent⟩ := run_budget input (2 * capacity.val) start last reply
      (BmLocator.initial_admitted syndromes buffers capacity budget paid bound room syndromeRoom) firstLive startFits returned
    change BmHonestLocator.Outcome support input last reply at outcome
    change last.2.1.limit = paid.limit at lastLimit
    change last.2.1.used.val + chargesRemaining last * input.cost.val ≤
      paid.used.val + chargesRemaining start * input.cost.val at spent
    have lastFits : last.2.1.used.val + chargesRemaining last * input.cost.val ≤ last.2.1.limit.val := by
      rw [lastLimit]
      exact spent.trans startFits
    rcases last with ⟨iter, finalMeter, connection, previous, saved, degree, previousLen, shift, scale⟩
    rcases outcome with ⟨error, chargedMeter, active, failed, _⟩ | ⟨_, _, _, rfl⟩
    · obtain ⟨next, ok, _, _, _⟩ := paid_iteration input
        (iter, finalMeter, connection, previous, saved, degree, previousLen, shift, scale)
        active lastLive lastFits
      change stepCharge iter.start finalMeter input.cost = (.Ok (), next) at ok
      rw [ok] at failed
      cases failed
    · refine ⟨degree, rfl, lastLive, lastLimit.trans firstLimit, ?_⟩
      change finalMeter.used.val ≤ _
      have debit : paid.used.val + chargesRemaining start * input.cost.val =
          meter.used.val + max 1 (2 * capacity.val) * units := by
        rw [remaining, inputPrice, firstUsed, ← identity, Nat.add_mul, Nat.one_mul, Nat.add_assoc]
      rw [debit] at spent
      exact (Nat.le_add_right ..).trans spent

end BulksketchBridge.PortableFrontPayment
