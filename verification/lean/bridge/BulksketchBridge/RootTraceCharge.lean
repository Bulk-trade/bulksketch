import BulksketchBridge.RootWorkBudgetNative
import BulksketchBridge.RootRunPrice
import BulksketchBridge.StageCharge

namespace BulksketchBridge.WorkMeter

open Aeneas Aeneas.Std
open bulksketch.types
open BulksketchProofs.Resource

/-- Sufficient remaining source work pays the exact charge, preserving the
    limit and a live meter even when the addition reaches the exact limit. -/
def ActualNativeWorkMeterPaid : Prop :=
  ∀ (meter : GeneratedMeter) (amount : U64),
    meter.exhausted = false → meter.used.val + amount.val ≤ meter.limit.val →
    ∃ paid : GeneratedMeter,
      bulksketch.types.WorkMeter.charge meter amount = .ok (.Ok (), paid) ∧
      paid.used.val = meter.used.val + amount.val ∧
      paid.limit = meter.limit ∧ paid.exhausted = false

theorem native_work_meter_paid : ActualNativeWorkMeterPaid := by
  intro meter amount live fits
  have success : ((toModel meter).charge (toUInt64 amount)).2 = true := by
    apply (BulksketchProofs.Resource.WorkMeter.charge_success_iff _ _).mpr
    exact ⟨live, by simpa only [toModel, toUInt64_toNat] using fits⟩
  obtain ⟨paid, ran, paidModel⟩ := charge_refines meter amount
  rw [success] at ran
  have update := (toModel meter).charge_eq_of_success (toUInt64 amount) success
  have used := (toModel meter).used_on_success (toUInt64 amount) success
  have usedExact : paid.used.val = meter.used.val + amount.val := by
    rw [← paidModel] at used
    simpa only [toModel, toUInt64_toNat] using used
  rw [update] at paidModel
  have limit : paid.limit = meter.limit :=
    toUInt64_injective (congrArg BulksketchProofs.Resource.WorkMeter.limit paidModel)
  have active : paid.exhausted = false :=
    (congrArg BulksketchProofs.Resource.WorkMeter.exhausted paidModel).trans live
  exact ⟨paid, ran, usedExact, limit, active⟩

/-- An exhausted source meter or a charge larger than its remaining
    budget returns the original denial and leaves usage unchanged. -/
def ActualNativeWorkMeterDenied : Prop :=
  ∀ (meter : GeneratedMeter) (amount : U64),
    (meter.exhausted = true ∨ meter.limit.val < meter.used.val + amount.val) →
    bulksketch.types.WorkMeter.charge meter amount =
      .ok (.Err .WorkLimitExceeded, { meter with exhausted := true })

theorem native_work_meter_denied : ActualNativeWorkMeterDenied := by
  intro meter amount denied
  have failed : ((toModel meter).charge (toUInt64 amount)).2 = false := by
    apply Bool.eq_false_iff.mpr
    intro success
    have admitted := (BulksketchProofs.Resource.WorkMeter.charge_success_iff _ _).mp success
    rcases denied with prior | over
    · have active : meter.exhausted = false := admitted.1
      rw [prior] at active
      contradiction
    · have fits : meter.used.val + amount.val ≤ meter.limit.val := by
        simpa only [toModel, toUInt64_toNat] using admitted.2
      exact (Nat.not_lt_of_ge fits) over
  obtain ⟨final, ran, finalModel⟩ := charge_refines meter amount
  rw [failed] at ran
  rw [(toModel meter).charge_eq_of_failure (toUInt64 amount) failed] at finalModel
  have finalEq : final = { meter with exhausted := true } :=
    toModel_injective finalModel
  rw [finalEq] at ran
  exact ran

#print axioms native_work_meter_paid
#print axioms native_work_meter_denied

end BulksketchBridge.WorkMeter

namespace BulksketchBridge.RootRun

open Aeneas Aeneas.Std RootWorkBudget WorkSchedule
open bulksketch.decode.work bulksketch.decode.roots bulksketch.types

/-- The exact original Trace, SplitCheck and GCD price tags at admitted
    u16 degree. These are the prices used by non-affine direction search. -/
def ActualNativeTraceSearchPrices : Prop :=
  ∀ degree : Usize, degree.val ≤ 65535 →
    (∃ trace : U64, WorkScheduleV1.cost (.Trace degree) = .ok (.Ok trace) ∧ trace.val = traceUnits degree.val) ∧
    (∃ check : U64, WorkScheduleV1.cost (.SplitCheck degree) = .ok (.Ok check) ∧ check.val = splitCheckUnits degree.val) ∧
    (∃ gcd : U64, WorkScheduleV1.cost (.Gcd degree) = .ok (.Ok gcd) ∧ gcd.val = gcdUnits degree.val)

theorem native_trace_search_prices : ActualNativeTraceSearchPrices := by
  intro degree admitted
  obtain ⟨_, trace, check, gcd, _, _⟩ := native_root_node_prices degree admitted
  exact ⟨trace, check, gcd⟩

/-- The original Roots charge wrapper submits the exact native price,
    preserving its success and complete meter frame. -/
def ActualNativeRootsPaidCharge : Prop :=
  ∀ (meter : WorkMeter) (operation : Charge) (amount : U64) (units : Nat),
    WorkScheduleV1.cost operation = .ok (.Ok amount) → amount.val = units →
    meter.exhausted = false → meter.used.val + units ≤ meter.limit.val →
    ∃ paid : WorkMeter,
      charge meter operation = .ok (.Ok (), paid) ∧
      paid.used.val = meter.used.val + units ∧ paid.limit = meter.limit ∧ paid.exhausted = false

theorem native_roots_paid_charge : ActualNativeRootsPaidCharge := by
  intro meter operation amount units priced value live fits
  have wrapper := roots_charge_returns meter operation (.Ok amount) priced
  rw [← StageCharge.meter_charge_refines] at wrapper
  obtain ⟨paid, ran, used, limit, active⟩ :=
    BulksketchBridge.WorkMeter.native_work_meter_paid meter amount live (by rwa [value])
  exact ⟨paid, wrapper.trans ran, by rwa [value] at used, limit, active⟩

/-- A successful three-way source price can be paid directly from its
    mathematical degree envelope. -/
def ActualNativeTraceSearchCharges : Prop :=
  ∀ (meter : WorkMeter) (degree : Usize), degree.val ≤ 65535 → meter.exhausted = false →
    let pays := fun (operation : Charge) (units : Nat) =>
      meter.used.val + units ≤ meter.limit.val →
      ∃ paid : WorkMeter, charge meter operation = .ok (.Ok (), paid) ∧
        paid.used.val = meter.used.val + units ∧ paid.limit = meter.limit ∧ paid.exhausted = false
    pays (.Trace degree) (traceUnits degree.val) ∧
      pays (.SplitCheck degree) (splitCheckUnits degree.val) ∧ pays (.Gcd degree) (gcdUnits degree.val)

theorem native_trace_search_charges : ActualNativeTraceSearchCharges := by
  intro meter degree admitted live pays
  obtain ⟨⟨trace, traceCall, traceValue⟩, ⟨check, checkCall, checkValue⟩, ⟨gcd, gcdCall, gcdValue⟩⟩ :=
    native_trace_search_prices degree admitted
  exact ⟨native_roots_paid_charge meter (.Trace degree) trace (traceUnits degree.val) traceCall traceValue live,
    native_roots_paid_charge meter (.SplitCheck degree) check (splitCheckUnits degree.val) checkCall checkValue live,
    native_roots_paid_charge meter (.Gcd degree) gcd (gcdUnits degree.val) gcdCall gcdValue live⟩

/-- Each chronological source charge is retained in the accounting trace. -/
inductive PaidSourceCharges : WorkMeter → List (Charge × Nat) → WorkMeter → Prop where
  | empty (meter : WorkMeter) : PaidSourceCharges meter [] meter
  | cons {meter paid final : WorkMeter} {operation : Charge} {units : Nat} {rest : List (Charge × Nat)} :
      charge meter operation = .ok (.Ok (), paid) →
      paid.used.val = meter.used.val + units → paid.limit = meter.limit → paid.exhausted = false →
      PaidSourceCharges paid rest final →
      PaidSourceCharges meter ((operation, units) :: rest) final

/-- Admission for the total chronological price implies every original
    source charge is paid exactly and the full sequence stays within its
    initial work limit. -/
theorem native_roots_paid_sequence (meter : WorkMeter) (entries : List (Charge × Nat))
    (priced : ∀ entry ∈ entries, ∃ amount : U64,
      WorkScheduleV1.cost entry.1 = .ok (.Ok amount) ∧ amount.val = entry.2)
    (live : meter.exhausted = false)
    (fits : meter.used.val + (entries.map Prod.snd).sum ≤ meter.limit.val) :
    ∃ final : WorkMeter, PaidSourceCharges meter entries final ∧
      final.used.val = meter.used.val + (entries.map Prod.snd).sum ∧
      final.limit = meter.limit ∧ final.exhausted = false := by
  induction entries generalizing meter with
  | nil =>
    exact ⟨meter, .empty meter, by simp, rfl, live⟩
  | cons entry tail ih =>
    obtain ⟨amount, price, value⟩ := priced entry List.mem_cons_self
    simp only [List.map_cons, List.sum_cons] at fits
    obtain ⟨paid, ran, used, limit, active⟩ :=
      native_roots_paid_charge meter entry.1 amount entry.2 price value live (by omega)
    obtain ⟨final, trace, total, finalLimit, finalActive⟩ :=
      ih paid (fun op inTail => priced op (List.mem_cons_of_mem _ inTail)) active
        (by rw [used, limit]; omega)
    exact ⟨final, .cons ran used limit active trace,
      by simpa only [List.map_cons, List.sum_cons, ← Nat.add_assoc, ← used] using total,
      finalLimit.trans limit, finalActive⟩

/-- One non-affine direction attempt pays Trace and GCD, and pays the
    source split check only while the factor remains unchecked. -/
def ActualNativeTraceAttemptCharges : Prop :=
  ∀ (roots : Roots) (meter : WorkMeter), roots.degree.val ≤ 65535 → meter.exhausted = false →
    let degree := roots.degree.val
    let checking := if roots.checked then 0 else splitCheckUnits degree
    meter.used.val + traceUnits degree + checking + gcdUnits degree ≤ meter.limit.val →
    ∃ afterTrace afterCheck afterGcd : WorkMeter,
      charge meter (.Trace roots.degree) = .ok (.Ok (), afterTrace) ∧
      (if roots.checked then afterCheck = afterTrace
        else charge afterTrace (.SplitCheck roots.degree) = .ok (.Ok (), afterCheck)) ∧
      charge afterCheck (.Gcd roots.degree) = .ok (.Ok (), afterGcd) ∧
      afterTrace.used.val = meter.used.val + traceUnits degree ∧
      afterCheck.used.val = afterTrace.used.val + checking ∧
      afterGcd.used.val = meter.used.val + traceUnits degree + checking + gcdUnits degree ∧
      afterTrace.limit = meter.limit ∧ afterCheck.limit = meter.limit ∧ afterGcd.limit = meter.limit ∧
      afterTrace.exhausted = false ∧ afterCheck.exhausted = false ∧ afterGcd.exhausted = false

theorem native_trace_attempt_charges : ActualNativeTraceAttemptCharges := by
  intro roots meter admitted live degree checking fits
  dsimp only [degree] at fits
  obtain ⟨paidTrace, _, _⟩ := native_trace_search_charges meter roots.degree admitted live
  obtain ⟨afterTrace, traceCall, traceUsed, traceLimit, traceLive⟩ := paidTrace (by omega)
  obtain ⟨afterCheck, checkCall, checkUsed, checkLimit, checkLive⟩ :
      ∃ afterCheck : WorkMeter,
        (if roots.checked then afterCheck = afterTrace
          else charge afterTrace (.SplitCheck roots.degree) = .ok (.Ok (), afterCheck)) ∧
        afterCheck.used.val = afterTrace.used.val + checking ∧
        afterCheck.limit = meter.limit ∧ afterCheck.exhausted = false := by
    cases checked : roots.checked with
    | false =>
      obtain ⟨_, paidCheck, _⟩ := native_trace_search_charges afterTrace roots.degree admitted traceLive
      have room : afterTrace.used.val + splitCheckUnits degree ≤ afterTrace.limit.val := by
        rw [traceUsed, traceLimit]
        dsimp only [degree]
        simp only [checking, checked, degree, Bool.false_eq_true, ite_false] at fits
        omega
      obtain ⟨afterCheck, ran, used, limit, active⟩ := paidCheck room
      exact ⟨afterCheck, by simp only [Bool.false_eq_true, ite_false]; exact ran,
        by simpa only [checking, checked, Bool.false_eq_true, ite_false] using used,
        limit.trans traceLimit, active⟩
    | true =>
      exact ⟨afterTrace, by simp only [ite_true],
        by simp only [checking, checked, ite_true, Nat.add_zero], traceLimit, traceLive⟩
  obtain ⟨_, _, paidGcd⟩ := native_trace_search_charges afterCheck roots.degree admitted checkLive
  obtain ⟨afterGcd, gcdCall, gcdUsed, gcdLimit, gcdLive⟩ := paidGcd (by
    rw [checkUsed, traceUsed, checkLimit]
    exact fits)
  exact ⟨afterTrace, afterCheck, afterGcd, traceCall, checkCall, gcdCall, traceUsed, checkUsed,
    by rw [gcdUsed, checkUsed, traceUsed], traceLimit, checkLimit, gcdLimit.trans checkLimit,
    traceLive, checkLive, gcdLive⟩

/-- The direction search reserves one Trace/GCD pair per possible
    remaining direction and at most one initial split check. -/
def traceSearchUnits (degree direction : Nat) (checked : Bool) : Nat :=
  (64 - direction) * (traceUnits degree + gcdUnits degree) +
    if checked then 0 else splitCheckUnits degree

theorem trace_search_units_step (degree direction : Nat) (checked : Bool) (inside : direction < 64) :
    traceSearchUnits degree direction checked =
      traceUnits degree + (if checked then 0 else splitCheckUnits degree) + gcdUnits degree +
        traceSearchUnits degree (direction + 1) true := by
  unfold traceSearchUnits
  rw [show 64 - direction = 1 + (64 - (direction + 1)) by omega, Nat.add_mul, Nat.one_mul]
  simp only [ite_true, Nat.add_zero]
  omega

#print axioms trace_search_units_step
#print axioms native_trace_attempt_charges
#print axioms native_trace_search_prices
#print axioms native_roots_paid_charge
#print axioms native_trace_search_charges
#print axioms native_roots_paid_sequence

end BulksketchBridge.RootRun
