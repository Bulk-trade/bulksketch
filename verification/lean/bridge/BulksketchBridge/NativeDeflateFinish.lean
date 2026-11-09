import BulksketchBridge.NativeDeflate
import BulksketchBridge.DeflatePrice
import BulksketchBridge.AffinePredictor

namespace BulksketchBridge.Deflation

open Aeneas Aeneas.Std Result DenseCoefficient SliceKernels Algebra.Gf64
open bulksketch.backend.contract bulksketch.decode.scratch bulksketch.decode.stages
open bulksketch.decode.row bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

structure FinalState where
  index : Nat
  locator : Slice U64
  quotient : Slice U64
  degree : Usize

inductive FinalBranch (frame : DeflateFrame) (roots : Slice U64) (final : FinalState) :
    Result DeflateAnswer → Prop
  | success (exhausted : final.index = roots.length) :
      FinalBranch frame roots final (startOutput frame final.locator final.quotient final.degree)
  | reject (active : final.index < roots.length)
      (invalid : ¬ (slicePolynomial (prefixSlice final.locator (final.degree.val + 1))).IsRoot
        (toField roots[final.index]!.bv)) :
      FinalBranch frame roots final
        (.ok (rejectOutput frame final.locator
          (syntheticOutput final.locator final.quotient roots[final.index]! final.degree)))

theorem trace_final {frame : DeflateFrame} {roots : Slice U64} {index : Nat}
    {locator quotient : Slice U64} {degree : Usize} {result : Result DeflateAnswer}
    (trace : DeflateTrace frame roots index locator quotient degree result) :
    ∃ final : FinalState,
      index ≤ final.index ∧ final.degree.val + final.index = degree.val + index ∧
      final.locator.length = locator.length ∧ final.quotient.length = quotient.length ∧
      FinalBranch frame roots final result := by
  induction trace with
  | exhausted index locator quotient degree atEnd =>
    exact ⟨⟨index, locator, quotient, degree⟩, le_rfl, rfl, rfl, rfl, .success atEnd⟩
  | rejected index locator quotient degree active invalid =>
    exact ⟨⟨index, locator, quotient, degree⟩, le_rfl, rfl, rfl, rfl, .reject active invalid⟩
  | accepted index locator quotient degree lower result _ decreased _ _ ih =>
    obtain ⟨final, progress, balance, locLen, qLen, branch⟩ := ih
    rw [RebuiltLfsr.restore_length] at locLen
    rw [synthetic_output_length] at qLen
    exact ⟨final, by omega, by omega, locLen, qLen, branch⟩

def finishedRoots (roots : bulksketch.decode.roots.Roots) (degree : Usize) :
    bulksketch.decode.roots.Roots :=
  RootSetup.startedRoots roots degree (roots.v3 && decide (3 ≤ degree.val ∧ degree.val ≤ 18))

theorem start_output_normal (frame : DeflateFrame) (locator quotient : Slice U64)
    (degree : Usize) (bounded : RootSetup.RootStartBounds degree
      (joinedWorkspace frame locator quotient)) :
    startOutput frame locator quotient degree = .ok
      (.Ok (some (ClosedLeafAdvance.stageFor (finishedRoots frame.roots degree))),
        finishedRoots frame.roots degree,
        RootSetup.startedWorkspace degree (joinedWorkspace frame locator quotient), workspaceParts) := by
  rw [start_output_refines frame locator quotient degree bounded,
    AffinePreferred.root_start_preference, bind_ok]
  rfl

private theorem entry_start_bounds {K : Type} (self : Execution bulksketch.field.Gf64 K)
    (workspace : RowWorkspace) (width : Nat) (state : FinalState)
    (widthRoom : width ≤ workspace.bm.length) (degreeRoom : state.degree.val < width)
    (polynomialRoom : state.degree.val < workspace.polynomials.length) :
    RootSetup.RootStartBounds state.degree
      (joinedWorkspace (deflateFrame self workspace width) state.locator state.quotient) := by
  have bmLen : (joinedWorkspace (deflateFrame self workspace width) state.locator state.quotient).bm.length =
      workspace.bm.length :=
    BmEntry.splitBack_length workspace.bm width _
  have bmMax : workspace.bm.length ≤ Usize.max := Slice.length_ineq workspace.bm
  exact ⟨by omega, fun _ => ⟨polynomialRoom, by omega⟩⟩

def ActualNativeDeflateFinish : Prop :=
  ∀ {K : Type} (field : bulksketch.field.BinaryField bulksketch.field.Gf64)
    (kernels : BulkKernels K bulksketch.field.Gf64)
    (_mul : ∀ a b, kernels.ArithmeticInst.mul a b = .ok (mulWord a b))
    (self : Execution bulksketch.field.Gf64 K) (input : RowInput)
    (workspace : RowWorkspace) (meter : WorkMeter),
    ((StageCharge.chargeResult meter (deflateCost self.degree)).1 = .Ok () →
      DeflateBounds self input workspace ∧ self.degree.val < workspace.polynomials.length) →
    let native := Execution.deflate field kernels self input workspace meter
    match StageCharge.chargeResult meter (deflateCost self.degree) with
    | (.Err error, meter1) => native = .ok (.Err error, self, workspace, id, meter1)
    | (.Ok (), meter1) =>
      let width := input.difference.length + 1
      let roots := prefixSlice workspace.roots self.hits.val
      let frame := deflateFrame self workspace width
      ∃ final : FinalState,
        final.degree.val + final.index = self.degree.val ∧
        final.locator.length = width ∧ final.quotient.length = width ∧
        ((final.index = self.hits.val ∧
          let updated := finishedRoots self.roots final.degree
          native = .ok (.Ok (.Ok (some (ClosedLeafAdvance.stageFor updated))),
            { self with roots := updated },
            RootSetup.startedWorkspace final.degree (joinedWorkspace frame final.locator final.quotient),
            id, meter1)) ∨
        (final.index < self.hits.val ∧
          ¬ (slicePolynomial (prefixSlice final.locator (final.degree.val + 1))).IsRoot
            (toField roots[final.index]!.bv) ∧
          native = .ok (.Ok (.Err .InvalidLocator), self,
            joinedWorkspace frame final.locator
              (syntheticOutput final.locator final.quotient roots[final.index]! final.degree),
            id, meter1)))

theorem native_deflate_finish : ActualNativeDeflateFinish := by
  intro K field kernels mul self input workspace meter admitted
  have stage := native_deflate field kernels mul self input workspace meter (deflateCost self.degree)
    (deflate_price self.degree) (fun h => (admitted h).1)
  cases charged : StageCharge.chargeResult meter (deflateCost self.degree) with
  | mk response finalMeter =>
    cases response with
    | Err error =>
      simpa only [charged] using stage
    | Ok empty =>
      cases empty
      rw [charged] at stage
      have ready : (StageCharge.chargeResult meter (deflateCost self.degree)).1 = .Ok () := by rw [charged]
      obtain ⟨⟨bmRoom, _, _, rootsRoom⟩, polyRoom⟩ := admitted ready
      obtain ⟨result, trace, native⟩ := stage
      obtain ⟨final, _, balance, locLen, qLen, branch⟩ := trace_final trace
      have degreeBound : final.degree.val ≤ self.degree.val := by omega
      have rootLength : (prefixSlice workspace.roots self.hits.val).length = self.hits.val := by
        rw [RebuiltLfsr.prefix_length, Nat.min_eq_left rootsRoom]
      rw [RebuiltLfsr.prefix_length, Nat.min_eq_left (by omega)] at locLen
      rw [RebuiltLfsr.prefix_length, BmEntry.tail_length, Nat.min_eq_left (by omega)] at qLen
      refine ⟨final, by omega, locLen, qLen, ?_⟩
      cases branch with
      | success exhausted =>
        rw [rootLength] at exhausted
        left
        refine ⟨exhausted, ?_⟩
        have bounded := entry_start_bounds self workspace (input.difference.length + 1) final
          (by omega) (by have := (admitted ready).1.2.1; omega) (by omega)
        rw [native, start_output_normal _ _ _ _ bounded]
        simp only [wrapDeflate, bind_ok]
        dsimp! only
        rfl
      | reject active invalid =>
        rw [rootLength] at active
        right
        refine ⟨active, invalid, ?_⟩
        rw [native]
        simp only [wrapDeflate, rejectOutput, bind_ok]
        dsimp! only
        cases self
        rfl

#print axioms trace_final
#print axioms start_output_normal
#print axioms native_deflate_finish

end BulksketchBridge.Deflation
