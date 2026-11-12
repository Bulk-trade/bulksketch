import Arithmetic.RowConfigurationGenerated
import BulksketchBridge.DegreeProbeRuntimeState
import BulksketchBridge.RootSetup

namespace BulksketchBridge.RowConfiguration

open Aeneas.Std ExecutionDriverRuntime DegreeProbeRuntime
open bulksketch.backend.contract bulksketch.decode.stages bulksketch.decode.roots
open bulksketch.decode.row bulksketch.decode.degree_probe bulksketch.types
open bulksketch.decode.stages.BinaryDecoder.Insts.BulksketchDecodeRowRowDecoderFKExecution (begin)

set_option maxRecDepth 4096

def initialRoots : Roots where
  pending := 0#usize
  stride := 0#usize
  degree := 0#usize
  direction := 0#u32
  checked := false
  trace_len := 0#usize
  gcd_len := 0#usize
  count := 0#usize
  attempts := 0#usize
  gcd_degree := 0#usize
  splitter_seed := 0#u64
  v3 := false
  closed_form := false
  solved_count := 0#usize
  affine := false
  affine_ready := false
  affine_base := 0#u64
  affine_rank := 0#usize

def initialExecution {F K : Type} (budget : RowBudget) : Execution F K where
  budget := budget
  state := .Running .Reconstruction
  degree := 0#usize
  hits := 0#usize
  roots := initialRoots
  v3 := false
  degree_probe := none
  marker := ()

def ActualRowBegin : Prop :=
  ∀ {F K : Type} (field : bulksketch.field.BinaryField F) (kernel : BulkKernels K F) (budget : RowBudget),
    begin field kernel budget = .ok (initialExecution budget)

theorem begin_refines : ActualRowBegin := by
  intro F K field kernel budget
  simp only [begin, Roots.Insts.CoreDefaultDefault.default, core.default.DefaultBool.default, bind_ok]
  rfl

def ActualRowSetSeed : Prop :=
  ∀ {F K : Type} (field : bulksketch.field.BinaryField F) (kernel : BulkKernels K F)
    (self : Execution F K) (seed : U64),
    Execution.set_splitter_seed field kernel self seed =
      .ok { self with roots := { self.roots with splitter_seed := seed } }

theorem set_seed_refines : ActualRowSetSeed := by
  intro F K field kernel self seed
  rw [Execution.set_splitter_seed, RootSetup.root_configuration_refines.2.2 self.roots seed, bind_ok]

def ActualRowRestart : Prop :=
  ∀ {F K : Type} (field : bulksketch.field.BinaryField F) (kernel : BulkKernels K F)
    (self : Execution F K) (budget : RowBudget) (seed : U64),
    Execution.restart field kernel self budget seed =
      .ok { initialExecution budget with roots := { initialRoots with splitter_seed := seed } }

theorem restart_refines : ActualRowRestart := by
  intro F K field kernel self budget seed
  rw [Execution.restart, begin_refines field kernel budget, bind_ok, set_seed_refines field kernel]
  rfl

def ActualRowEnableV3 : Prop :=
  ∀ {F K : Type} (field : bulksketch.field.BinaryField F) (kernel : BulkKernels K F) (self : Execution F K),
    Execution.enable_v3 field kernel self = (do
      let width ← field.BITS
      .ok { self with
        v3 := true
        roots := { self.roots with
          v3 := true
          closed_form := if width = 64#u32 then true else self.roots.closed_form } })

theorem enable_v3_refines : ActualRowEnableV3 := by
  intro F K field kernel self
  rw [Execution.enable_v3, RootSetup.root_configuration_refines.1 self.roots, bind_ok]
  congr 1
  funext width
  by_cases same : width = 64#u32
  · rw [ite_eq_left same, RootSetup.root_configuration_refines.2.1, bind_ok, ite_eq_left same]
  · simp only [same, ite_false]

def ActualVerificationCount : Prop :=
  ∀ {F K : Type} (field : bulksketch.field.BinaryField F) (kernel : BulkKernels K F) (self : Execution F K),
    Execution.verification_count field kernel self = .ok self.roots.count

theorem verification_count_refines : ActualVerificationCount := by
  intro F K field kernel self
  rfl

def ActualStartDegrees : Prop :=
  ∀ {F K : Type} (field : bulksketch.field.BinaryField F) (kernel : BulkKernels K F)
    (self : Execution F K) (capacity : Usize),
    Execution.start_degrees field kernel self capacity = (do
      if self.v3 then
        let width ← field.BITS
        if width = 64#u32 then
          if 3 ≤ self.budget.nonzero.val ∧ 3 ≤ capacity.val then
            .ok { self with state := .Running .GuardThree, degree_probe := some initialState }
          else .ok { self with degree_probe := none }
        else .ok self
      else .ok self)

theorem start_degrees_refines : ActualStartDegrees := by
  intro F K field kernel self capacity
  cases enabled : self.v3
  · simp only [Execution.start_degrees, enabled, Bool.false_eq_true, ite_false]
  · simp only [Execution.start_degrees, enabled, ite_true]
    congr 1
    funext width
    by_cases exactWidth : width = 64#u32
    · simp only [exactWidth, ite_true, new_refines self.budget capacity, bind_ok, expectedNew]
      by_cases ready : 3 ≤ self.budget.nonzero.val ∧ 3 ≤ capacity.val
      · simp only [ready, and_self, ite_true, DegreeProbe.next_stage, initialState,
          bind_ok, core.option.Option.expect, Result.ofOption]
      · simp only [ready, ite_false]
    · simp only [exactWidth, ite_false]

def ActualRejectUpper : Prop :=
  ∀ {F K : Type} (field : bulksketch.field.BinaryField F) (kernel : BulkKernels K F)
    (self : Execution F K) (capacity : Usize),
    Execution.reject_upper field kernel self capacity =
      .ok (match self.degree_probe with
        | none => { self with state := .Failed .InvalidLocator }
        | some probe =>
          if probe.degree.val = 3 ∧ 4 ≤ capacity.val ∧ 4 ≤ self.budget.nonzero.val then
            { self with
              state := .Running .GuardFour
              roots := { self.roots with count := 0#usize }
              degree_probe := some (expectedReject probe capacity self.budget) }
          else
            { self with
              state := .Running .Reconstruction
              roots := { self.roots with count := 0#usize }
              degree_probe := none })

theorem reject_upper_refines : ActualRejectUpper := by
  intro F K field kernel self capacity
  cases probeState : self.degree_probe with
  | none => simp only [Execution.reject_upper, probeState]
  | some probe =>
    simp only [Execution.reject_upper, probeState, reject_refines probe capacity self.budget,
      bind_ok, next_stage_refines (expectedReject probe capacity self.budget)]
    by_cases ready : probe.degree.val = 3 ∧ 4 ≤ capacity.val ∧ 4 ≤ self.budget.nonzero.val
    · rw [ite_eq_left ready]
      simp only [expectedReject, ready, and_self, ite_true, core.option.Option.expect, Result.ofOption, bind_ok, optionEq]
      simp [Stage.Insts.CoreCmpPartialEqStage.eq, Stage.read_discriminant]
    · rw [ite_eq_right ready]
      simp only [expectedReject, ready, ite_false, core.option.Option.expect, Result.ofOption, bind_ok, optionEq]
      simp [Stage.Insts.CoreCmpPartialEqStage.eq, Stage.read_discriminant]

#print axioms begin_refines
#print axioms restart_refines
#print axioms start_degrees_refines
#print axioms reject_upper_refines

end BulksketchBridge.RowConfiguration
