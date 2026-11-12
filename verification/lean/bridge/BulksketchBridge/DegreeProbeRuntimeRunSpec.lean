import BulksketchBridge.DegreeProbeRuntimeStateSpec
import BulksketchBridge.DegreeProbeRuntime
import BulksketchBridge.StageChargeSpec
import BulksketchBridge.NewtonGuardSpec
import BulksketchBridge.NormalizeSpec
import BulksketchBridge.ClosedLeafWindows
import BulksketchBridge.PortableEncodingChallenges
import BulksketchBridge.QuarticSolveSpec
import BulksketchBridge.CertificateSpec


namespace BulksketchBridge.DegreeProbeRuntime

open Aeneas.Std DenseCoefficient RebuiltLfsr ClosedLeaf
open bulksketch.decode.degree_probe bulksketch.decode.row bulksketch.decode.scratch
open bulksketch.decode.work bulksketch.types bulksketch.backend.contract

abbrev fieldDictionary := bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField

inductive Phase where
  | guard | normalize | leaf | certificate | verify | canonicalize
  deriving DecidableEq

abbrev degreeWord (self : DegreeProbe) : Usize := core.convert.num.FromUsizeU8.from self.degree
abbrev countWord (self : DegreeProbe) : Usize := core.convert.num.FromUsizeU8.from self.count

def phaseStage (phase : Phase) (degree : Usize) : Stage :=
  match phase with
  | .guard => if degree = 3#usize then .GuardThree else .GuardFour
  | .normalize => if degree = 3#usize then .NewtonThree else .NewtonFour
  | .leaf => if degree = 3#usize then .LeafThree else .LeafFour
  | .certificate => .FactorVerification
  | .verify => .Verification
  | .canonicalize => .Canonicalization

def phasePrice (phase : Phase) (degree : Usize) (odd : Slice U64) (budget : RowBudget) : Charge :=
  match phase with
  | .guard => if degree = 3#usize then .GuardThree else .GuardFour
  | .normalize => if degree = 3#usize then .NewtonThree else .NewtonFour
  | .leaf => if degree = 3#usize then .LeafThree else .LeafFour
  | .certificate => .FactorVerification degree
  | .verify => .Verify odd.len budget.total
  | .canonicalize => .Canonicalize budget.total

def encodedWords (shape ids : Slice U64) : Slice U64 :=
  Slice.from (List.ofFn fun slot : Fin shape.length => PortableEncoding.foldColumn ids.val slot.val 0#u64)
    (by simp)

def CorrectEncoding {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) : Prop :=
  ∀ scratch roots, kernels.encode_nonzero scratch roots = .ok (encodedWords scratch roots)

abbrev RunResult := core.result.Result (Option Stage) DecodeError × DegreeProbe × RowWorkspace ×
  (RowWorkspace → RowWorkspace) × WorkMeter

abbrev resultOfState (state : DegreeProbe) (workspace : RowWorkspace) (meter : WorkMeter) : RunResult :=
  (.Ok state.next, state, workspace, id, meter)

/-- The original price is evaluated first. Its error and every meter error preserve the input state. -/
def paid (state : DegreeProbe) (workspace : RowWorkspace) (meter : WorkMeter)
    (operation : Charge) (body : WorkMeter → Result RunResult) : Result RunResult := do
  let cost ← WorkScheduleV1.cost operation
  let (charge, final) := StageCharge.chargeResult meter cost
  match charge with
  | .Err error => .ok (.Err error, state, workspace, id, final)
  | .Ok () => body final

structure Admitted (phase : Phase) (self : DegreeProbe) (odd : Slice U64) (workspace : RowWorkspace) : Prop where
  degreeCases : degreeWord self = 3#usize ∨ degreeWord self = 4#usize
  stage : self.next = some (phaseStage phase (degreeWord self))
  shape : match phase with
    | .guard => degreeWord self ≤ odd.length ∧ 11 ≤ workspace.polynomials.length
    | .normalize => 0 < odd.length ∧ 11 ≤ workspace.polynomials.length ∧
        (region workspace.polynomials 5 11)[5]! ≠ 0#u64
    | .leaf => 15 ≤ workspace.polynomials.length
    | .certificate => (countWord self).val = (degreeWord self).val ∧ 20 ≤ workspace.polynomials.length ∧
        (countWord self).val ≤ workspace.roots.length
    | .verify => (countWord self).val = (degreeWord self).val ∧ (countWord self).val ≤ workspace.roots.length ∧
        odd.length ≤ workspace.verification.length
    | .canonicalize => (countWord self).val = (degreeWord self).val ∧ (countWord self).val ≤ workspace.roots.length

/-- One paid phase. The speculative leaf keeps the exact selected native solve call. -/
noncomputable def phaseResult {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (phase : Phase) (self : DegreeProbe) (odd : Slice U64) (budget : RowBudget)
    (workspace : RowWorkspace) (meter : WorkMeter) : Result RunResult :=
  let degree := degreeWord self
  let count := countWord self
  let poly := workspace.polynomials
  let rejected := expectedReject self odd.len budget
  match phase with
  | .guard =>
    let (accepted, cleared) := NewtonGuard.expected odd degree (region poly 5 11)
    let updated := if accepted then {self with next := some (phaseStage .normalize degree)} else rejected
    .ok (resultOfState updated {workspace with polynomials := poly.setSlice! 5 cleared.val} meter)
  | .normalize =>
    let factor := Normalize.expectedOutput (region poly 5 11) odd[0]! degree.val (prefixSlice poly 5)
    .ok (resultOfState {self with next := some (phaseStage .leaf degree)}
      {workspace with polynomials := restorePrefix poly factor} meter)
  | .leaf => do
    let (outcome, words) ← bulksketch.decode.deg34.solve fieldDictionary kernels
      (prefixSlice poly (degree.val + 1)) (region poly 11 15)
    let updated := match outcome with
      | none => rejected
      | some found => {self with count := UScalar.cast .U8 found, next := some .FactorVerification}
    .ok (resultOfState updated {workspace with polynomials := poly.setSlice! 11 words.val} meter)
  | .certificate =>
    let candidates := region poly 11 (11 + count.val)
    let (accepted, product) := Certificate.expected (prefixSlice poly (degree.val + 1)) candidates (region poly 15 20)
    let withProduct := {workspace with polynomials := poly.setSlice! 15 product.val}
    if accepted then
      .ok (resultOfState {self with next := some .Verification}
        {withProduct with roots := restorePrefix workspace.roots candidates} meter)
    else .ok (resultOfState rejected withProduct meter)
  | .verify =>
    let verified := encodedWords (prefixSlice workspace.verification odd.length) (prefixSlice workspace.roots count.val)
    let updated := if verified = odd then {self with next := some .Canonicalization} else rejected
    .ok (resultOfState updated {workspace with verification := restorePrefix workspace.verification verified} meter)
  | .canonicalize =>
    .ok (resultOfState {self with next := none} {workspace with roots := canonicalize workspace.roots count.val} meter)

/-- The original stage returns exactly the priced transition, including its whole scratch frame. -/
def ActualDegreeProbeRun : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) (phase : Phase)
    (self : DegreeProbe) (odd : Slice U64) (budget : RowBudget) (workspace : RowWorkspace) (meter : WorkMeter),
    Cubic.CorrectArithmetic kernels → (phase = .verify → CorrectEncoding kernels) →
    Admitted phase self odd workspace →
    DegreeProbe.run fieldDictionary kernels self odd budget workspace meter =
      paid self workspace meter (phasePrice phase (degreeWord self) odd budget)
        (phaseResult kernels phase self odd budget workspace)

end BulksketchBridge.DegreeProbeRuntime
