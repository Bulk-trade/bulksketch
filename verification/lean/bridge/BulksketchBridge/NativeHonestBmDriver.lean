import BulksketchBridge.NativeCandidateDeflateDriver
import BulksketchBridge.BmBufferLayout
import BulksketchBridge.RootFactorValidity

namespace BulksketchBridge.ExecutionDriver

open Aeneas.Std ExecutionDriverRuntime Algebra.Gf64 Polynomial
open DenseCoefficient RebuiltLfsr BmEntry BmSyndromePolynomials SliceKernels Reconciliation
open bulksketch.backend.contract bulksketch.decode.stages bulksketch.decode.row
open bulksketch.decode.scratch bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 2500000

private theorem finish_bm_width (syndromes buffers : Slice U64) (capacity budget : Usize)
    (connection previous saved : Slice U64) (meter : WorkMeter) (reply : BmTerminal.Reply) :
    (BmLoop.finish (BmLocator.inputs syndromes buffers capacity budget) connection previous saved meter reply).2.1.length =
      buffers.length := by
  unfold BmLoop.finish BmLocator.inputs BmTerminal.joinBuffers
  exact splitBack_length ..

private theorem locator_words (words : Slice U64) (capacity degree : Nat)
    (room : capacity + 1 ≤ words.length) (degreeBound : degree ≤ capacity) :
    connectionPolynomial (prefixSlice words (capacity + 1)) degree =
      slicePolynomial (prefixSlice words (degree + 1)) := by
  ext i
  rw [connectionPolynomial, coeff_boundedPolynomial, prefix_coeff _ _ _ (by omega)]
  by_cases active : i < degree + 1
  · simp only [active, ite_true, prefixSlice, Slice.getElem!_Nat_eq, Slice.from_val,
      List.getElem!_eq_getElem?_getD, List.getElem?_take_of_lt (show i < capacity + 1 by omega)]
  · simp only [active, ite_false]

private theorem support_valid (support : Finset Field) (nonzero : (0 : Field) ∉ support) :
    RootRun.ValidFactor (supportLocator support) support.card := by
  have roots : (supportLocator support).roots = support.val := roots_prod_X_sub_C support
  have monic := supportLocator_monic support
  refine ⟨monic, supportLocator_natDegree support, ?_, roots.symm ▸ support.nodup, ?_⟩
  · apply Polynomial.Splits.prod
    intro root _
    exact Polynomial.Splits.X_sub_C root
  · intro point isRoot zero
    subst point
    have present := (mem_roots monic.ne_zero).mpr isRoot
    rw [roots] at present
    exact nonzero present

/-- The actual honest native BM stage latches a charge error or advances
    to candidate evaluation with the exact monic support locator. Its
    source constant-word check cannot reject an admitted nonzero support. -/
def ActualNativeHonestBmDriver : Prop :=
  ∀ (canonicalize : Canonicalize) {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    BmDiscrepancy.RawArithmetic kernels → BmDiscrepancy.ReduceArithmetic kernels →
    BmMutable.NativeMul kernels → BmTerminal.NativeInverse kernels →
    ∀ (self : Execution bulksketch.field.Gf64 K) (input : RowInput)
      (workspace : RowWorkspace) (initial : Slice U64) (meter : WorkMeter) (support : Finset Field),
    self.state = .Running .BerlekampMassey → self.degree_probe = none →
    (0 : Field) ∉ support → support.card ≤ self.budget.nonzero.val →
    self.budget.nonzero.val ≤ input.difference.length →
    3 * (input.difference.length + 1) ≤ workspace.bm.length →
    2 * input.difference.length + 1 ≤ workspace.syndromes.length →
    Reconstruction.Prefix input.difference initial workspace.syndromes (2 * input.difference.length + 1) →
    BmHonestLocator.Moments support workspace.syndromes (2 * input.difference.length) →
    ∃ reply : BmTerminal.Return,
      bulksketch.decode.bm.locator BmEntry.fieldDictionary kernels workspace.syndromes input.difference.len
        self.budget.nonzero workspace.bm meter = .ok reply ∧
      reply.2.1.length = workspace.bm.length ∧
      let written := { workspace with bm := reply.2.1 }
      match reply.1 with
      | .Err error =>
        nativeCandidateDriver canonicalize kernels self input workspace meter =
          .ok (.Err error, { self with state := .Error error }, written, id, reply.2.2)
      | .Ok (.Err _) => False
      | .Ok (.Ok degree) =>
        let updated := { self with degree }
        let factor := slicePolynomial (prefixSlice written.bm (degree.val + 1))
        nativeCandidateDriver canonicalize kernels self input workspace meter =
          .ok (.Ok (progress .BerlekampMassey updated),
            { updated with state := .Running .CandidateEvaluation }, written, id, reply.2.2) ∧
        degree.val = support.card ∧ factor = supportLocator support ∧
        RootRun.ValidFactor factor degree.val

theorem native_honest_bm_driver : ActualNativeHonestBmDriver := by
  intro canonicalize K kernels raw reduce mul inverse self input workspace initial meter support state noProbe
    noZero budgeted cap room syndromes reconstructed moments
  let capacity := Slice.len input.difference
  have capVal : capacity.val = input.difference.length := Slice.len_val ..
  obtain ⟨reply, ran, honest⟩ := BmHonestLocator.honest_locator_refines kernels raw reduce mul inverse
    support workspace.syndromes workspace.bm input.difference initial capacity self.budget.nonzero meter
    noZero budgeted (by rwa [capVal]) (by rwa [capVal]) (by rwa [capVal])
    (by rwa [capVal]) (by rwa [capVal])
  have width : reply.2.1.length = workspace.bm.length := by
    rcases honest with ⟨_, _, _, rfl⟩ | ⟨_, last, _, _, honest⟩
    · rfl
    · rcases last with ⟨iter, paid, connection, previous, saved, degree, len, shift, delta⟩
      rcases honest with ⟨error, charged, _, _, rfl⟩ | ⟨_, _, _, rfl⟩
      · exact finish_bm_width _ _ _ _ _ _ _ _ _
      · exact finish_bm_width _ _ _ _ _ _ _ _ _
  have driver : nativeCandidateDriver canonicalize kernels self input workspace meter = (do
      let result ← bmFrame self workspace reply.1 reply.2.1 reply.2.2
      Result.ok (transition .BerlekampMassey result)) := by
    unfold nativeCandidateDriver
    rw [run_next_refines RootRun.nativeCalls RootRun.nativeDivRem canonicalize RootSetup.gf64Dictionary kernels
      self input workspace meter, expectedRunNext, state]
    dsimp only
    rw [execute_refines RootRun.nativeCalls RootRun.nativeDivRem canonicalize RootSetup.gf64Dictionary
      kernels self .BerlekampMassey input workspace meter]
    unfold expectedExecute
    rw [noProbe]
    dsimp only
    change _ = _ at ran
    rw [ran, bind_ok]
    cases reply with
    | mk first rest => cases rest; rfl
  refine ⟨reply, ran, width, ?_⟩
  cases result : reply.1 with
  | Err error =>
    rw [driver, result]
    simp only [bmFrame, bind_ok, transition]
  | Ok success =>
    cases success with
    | Err reason =>
      rcases honest with ⟨_, _, _, rfl⟩ | ⟨_, last, _, _, honest⟩
      · cases result
      · rcases last with ⟨iter, paid, connection, previous, saved, degree, len, shift, delta⟩
        rcases honest with ⟨error, charged, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> cases result
    | Ok degree =>
      obtain ⟨degreeValue, connection⟩ := BmBufferLayout.actual_returned_locator kernels raw reduce mul inverse
        support workspace.syndromes workspace.bm input.difference initial capacity self.budget.nonzero
        meter reply degree noZero budgeted (by rwa [capVal]) (by rwa [capVal]) (by rwa [capVal])
        (by rwa [capVal]) (by rwa [capVal]) ran (by rw [result])
      let factor := slicePolynomial (prefixSlice reply.2.1 (degree.val + 1))
      have locator : factor = supportLocator support := by
        have wide : capacity.val + 1 ≤ reply.2.1.length := by rw [width, capVal]; omega
        have fits : degree.val ≤ capacity.val := by rw [degreeValue, capVal]; omega
        exact (locator_words reply.2.1 capacity.val degree.val wide fits).symm.trans connection
      have valid : RootRun.ValidFactor factor degree.val := by
        rw [locator, degreeValue]
        exact support_valid support noZero
      have positive : 0 < reply.2.1.length := by rw [width]; omega
      have leading : reply.2.1[0]! ≠ 0#u64 := by
        intro zero
        obtain ⟨_, _, _, _, nonzero⟩ := valid
        apply nonzero 0 ?_ rfl
        change factor.eval 0 = 0
        rw [← coeff_zero_eq_eval_zero]
        have count : degree.val + 1 ≤ reply.2.1.length := by rw [width, degreeValue]; omega
        change (slicePolynomial (prefixSlice reply.2.1 (degree.val + 1))).coeff 0 = _
        rw [prefix_coeff _ _ _ count, ite_eq_left (by omega : 0 < degree.val + 1), zero]
        exact toField_zero
      obtain ⟨word, read, exactWord⟩ := RawMulTable.normal_of_spec _ _
        (Slice.index_usize_spec reply.2.1 0#usize (by exact positive))
      have exactRead : Slice.index_usize reply.2.1 0#usize = .ok reply.2.1[0]! := by
        rw [read, exactWord]
        simp only [Slice.getElem!_Nat_eq, show (0#usize : Usize).val = 0 by rfl]
        exact congrArg Result.ok (List.Inhabited_getElem_eq_getElem! _ _ positive)
      refine ⟨?_, degreeValue, locator, valid⟩
      rw [driver, result]
      simp only [bmFrame, exactRead, leading, ite_false, bind_ok, transition]

#print axioms native_honest_bm_driver

end BulksketchBridge.ExecutionDriver
