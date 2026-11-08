import Arithmetic.ExecutionVerifyGenerated
import BulksketchBridge.ProbeVerificationSpec
import BulksketchBridge.VerifyDispatchSpec
import BulksketchBridge.StageChargeSpec

namespace BulksketchBridge.ExecutionVerify

open Aeneas.Std DegreeProbeRuntime DenseCoefficient RebuiltLfsr
open bulksketch.backend.contract bulksketch.decode.stages bulksketch.decode.row bulksketch.decode.scratch
open bulksketch.decode.work bulksketch.types

abbrev Reply := core.result.Result (core.result.Result (Option Stage) DecodeFailure) DecodeError
abbrev Return (F K : Type) := Reply × Execution F K × RowWorkspace × (RowWorkspace → RowWorkspace) × WorkMeter

def selects {F K : Type} (self : Execution F K) (input : RowInput) : Bool :=
  self.v3 && VerifyDispatch.selectsRebuilt self.roots.count.val input.difference.length

def priceTag {F K : Type} (self : Execution F K) (input : RowInput) : Charge :=
  if selects self input then .VerifyLfsr input.difference.len self.budget.total self.roots.count
  else .Verify input.difference.len self.budget.total

def selectedRoots {F K : Type} (self : Execution F K) (workspace : RowWorkspace) : Slice U64 :=
  prefixSlice workspace.roots self.roots.count.val

def rebuiltExpected (roots odd coefficients expected seed : Slice U64) (continued : Bool) :
    Bool × Slice U64 × Slice U64 :=
  let locator := locatorWords roots (prefixSlice coefficients (roots.length + 1))
  let agrees := decide (seed = prefixSlice odd seed.length)
  (agrees && continued,
    restorePrefix coefficients (if agrees then squareFrom locator 1 else locator),
    restorePrefix expected seed)

/-- Contracts specific to the selected rebuilt verifier. The recurrence result
is needed only when the seed agrees with the input prefix. -/
structure RebuiltAdmission {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots odd coefficients expected seed : Slice U64) (continued : Bool) : Prop where
  linear : linearLaw kernels
  square : squaringLaw kernels
  coefficientsRoom : roots.length < coefficients.length
  seedRoom : min roots.length odd.length ≤ expected.length
  seedLength : seed.length = min roots.length odd.length
  insert : kernels.insert_nonzero (zeroWords (prefixSlice expected seed.length)) roots = .ok seed
  recurrence : seed = prefixSlice odd seed.length →
    kernels.odd_recurrence_matches odd
      (squareFrom (locatorWords roots (prefixSlice coefficients (roots.length + 1))) 1) = .ok continued

def expected {F K : Type} (self : Execution F K) (input : RowInput) (workspace : RowWorkspace)
    (meter : WorkMeter) (cost : WorkSchedule.CostResult) (seed : Slice U64) (continued : Bool) : Return F K :=
  let (charge, final) := StageCharge.chargeResult meter cost
  match charge with
  | .Err error => (.Err error, self, workspace, id, final)
  | .Ok () =>
    let roots := selectedRoots self workspace
    let (valid, bm, verification) :=
      if selects self input then rebuiltExpected roots input.difference workspace.bm workspace.verification seed continued
      else
        let (accepted, updated) := ProbeVerification.expected input.difference roots workspace.verification
        (accepted, workspace.bm, updated)
    let reply := if valid then .Ok (.Ok (some .Canonicalization)) else .Ok (.Err .VerificationFailed)
    (reply, self, { workspace with bm := bm, verification := verification }, id, final)

structure Bounds {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (self : Execution bulksketch.field.Gf64 K) (input : RowInput) (workspace : RowWorkspace)
    (meter : WorkMeter) (cost : WorkSchedule.CostResult) (seed : Slice U64) (continued : Bool) : Prop where
  rootsRoom : (StageCharge.chargeResult meter cost).1 = .Ok () → self.roots.count.val ≤ workspace.roots.length
  rebuilt : (StageCharge.chargeResult meter cost).1 = .Ok () → selects self input = true →
    RebuiltAdmission kernels (selectedRoots self workspace) input.difference workspace.bm workspace.verification seed continued
  full : (StageCharge.chargeResult meter cost).1 = .Ok () → selects self input = false →
    (∀ x y, kernels.ArithmeticInst.mul x y = bulksketch.field.gf64.mul fieldDictionary x y) ∧
    (∀ x, kernels.ArithmeticInst.square x = bulksketch.field.gf64.square fieldDictionary x) ∧
    CorrectEncoding kernels ∧ ProbeVerification.Bounds input.difference (selectedRoots self workspace) workspace.verification

/-- The original stage fixes the price tag from native dispatch, preserves
every charge error, and changes only the scratch fields touched by the
selected verifier. Success transitions to canonicalization. -/
def ActualExecutionVerify : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (self : Execution bulksketch.field.Gf64 K) (input : RowInput) (workspace : RowWorkspace)
    (meter : WorkMeter) (cost : WorkSchedule.CostResult) (seed : Slice U64) (continued : Bool),
    WorkScheduleV1.cost (priceTag self input) = .ok cost →
    Bounds kernels self input workspace meter cost seed continued →
    Execution.verify fieldDictionary kernels self input workspace meter =
      .ok (expected self input workspace meter cost seed continued)

end BulksketchBridge.ExecutionVerify
