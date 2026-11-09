import BulksketchBridge.NativeDeflateFinish

namespace BulksketchBridge.Deflation

open Aeneas Aeneas.Std Result DenseCoefficient RebuiltLfsr SliceKernels Algebra.Gf64
open Polynomial
open bulksketch.backend.contract bulksketch.decode.scratch bulksketch.decode.stages
open bulksketch.decode.row bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

noncomputable def activeLocator (locator : Slice U64) (degree : Usize) : Polynomial Field :=
  slicePolynomial (prefixSlice locator (degree.val + 1))

noncomputable def rootProduct (roots : Slice U64) : Nat → Nat → Polynomial Field
  | _, 0 => 1
  | index, count + 1 =>
    (X + C (toField roots[index]!.bv)) * rootProduct roots (index + 1) count

private theorem copied_locator (locator quotient : Slice U64) (root : U64)
    (degree lower : Usize) (decreased : lower.val + 1 = degree.val)
    (locRoom : degree.val < locator.length) (qRoom : degree.val ≤ quotient.length) :
    activeLocator (restorePrefix locator (prefixSlice (syntheticOutput locator quotient root degree) degree.val)) lower =
      slicePolynomial (prefixSlice (syntheticOutput locator quotient root degree) degree.val) := by
  have length : (prefixSlice (syntheticOutput locator quotient root degree) degree.val).length =
      degree.val := by rw [prefix_length, synthetic_output_length, Nat.min_eq_left qRoom]
  have restore := DenseGcd.prefix_restored locator
    (prefixSlice (syntheticOutput locator quotient root degree) degree.val) (by rw [length]; omega)
  rw [length] at restore
  rw [activeLocator, decreased, restore]

/-- Every accepted source iteration removes exactly one linear factor. A
terminal rejection retains the locator after all earlier accepted factors. -/
theorem trace_residual_factorization {frame : DeflateFrame} {roots : Slice U64} {index : Nat}
    {locator quotient : Slice U64} {degree : Usize} {result : Result DeflateAnswer}
    (trace : DeflateTrace frame roots index locator quotient degree result)
    (locRoom : degree.val < locator.length) (qRoom : degree.val ≤ quotient.length) :
    ∃ final : FinalState, index ≤ final.index ∧ final.degree.val + final.index = degree.val + index ∧
      final.locator.length = locator.length ∧ final.quotient.length = quotient.length ∧
      activeLocator locator degree =
        rootProduct roots index (final.index - index) * activeLocator final.locator final.degree ∧
      FinalBranch frame roots final result := by
  induction trace with
  | exhausted index locator quotient degree atEnd =>
    exact ⟨⟨index, locator, quotient, degree⟩, le_rfl, rfl, rfl, rfl,
      by simp [rootProduct], .success atEnd⟩
  | rejected index locator quotient degree active invalid =>
    exact ⟨⟨index, locator, quotient, degree⟩, le_rfl, rfl, rfl, rfl,
      by simp [rootProduct], .reject active invalid⟩
  | accepted index locator quotient degree lower result _ decreased identity _ ih =>
    obtain ⟨final, progress, balance, locLen, qLen, product, branch⟩ := ih
      (by rw [restore_length]; omega) (by rw [synthetic_output_length]; omega)
    rw [restore_length] at locLen
    rw [synthetic_output_length] at qLen
    refine ⟨final, by omega, by omega, locLen, qLen, ?_, branch⟩
    have copy := copied_locator locator quotient roots[index]! degree lower decreased locRoom qRoom
    have count : final.index - index = (final.index - (index + 1)) + 1 := by omega
    calc
      activeLocator locator degree = (X + C (toField roots[index]!.bv)) *
          activeLocator (restorePrefix locator
            (prefixSlice (syntheticOutput locator quotient roots[index]! degree) degree.val)) lower := by
        rw [copy]
        exact identity
      _ = rootProduct roots index (final.index - index) * activeLocator final.locator final.degree := by
        rw [product, count, rootProduct, mul_assoc]

private theorem linear_eval_ne_zero (left right : U64) (different : left ≠ right) :
    (X + C (toField left.bv)).eval (toField right.bv) ≠ 0 := by
  intro zero
  simp only [eval_add, eval_X, eval_C] at zero
  rw [← toField_xor] at zero
  have bits : right.bv ^^^ left.bv = 0#64 := toField_injective (zero.trans toField_zero.symm)
  apply different
  apply U64.bv_eq_imp_eq
  exact (BitVec.xor_eq_zero_iff.mp bits).symm

private theorem product_eval_ne_zero (roots : Slice U64) (count index target : Nat)
    (prior : index + count ≤ target) (inside : target < roots.length)
    (distinct : ∀ i j, i < j → j < roots.length → roots[i]! ≠ roots[j]!) :
    (rootProduct roots index count).eval (toField roots[target]!.bv) ≠ 0 := by
  induction count generalizing index with
  | zero => simp [rootProduct]
  | succ count ih =>
    rw [rootProduct, eval_mul]
    exact mul_ne_zero (linear_eval_ne_zero _ _ (distinct index target (by omega) inside))
      (ih (index + 1) (by omega))

/-- Distinct supplied words that vanish in the original active locator cannot
produce an InvalidLocator branch. The residual passed to Roots.start times
the supplied linear factors is exactly the original active locator. -/
theorem trace_distinct_candidates_success {frame : DeflateFrame} {roots : Slice U64} {index : Nat}
    {locator quotient : Slice U64} {degree : Usize} {result : Result DeflateAnswer}
    (trace : DeflateTrace frame roots index locator quotient degree result)
    (locRoom : degree.val < locator.length) (qRoom : degree.val ≤ quotient.length)
    (supplied : ∀ j, index ≤ j → j < roots.length →
      (activeLocator locator degree).IsRoot (toField roots[j]!.bv))
    (distinct : ∀ i j, i < j → j < roots.length → roots[i]! ≠ roots[j]!) :
    ∃ final : FinalState, final.index = roots.length ∧
      final.degree.val + (roots.length - index) = degree.val ∧
      final.locator.length = locator.length ∧ final.quotient.length = quotient.length ∧
      activeLocator locator degree =
        rootProduct roots index (roots.length - index) * activeLocator final.locator final.degree ∧
      result = startOutput frame final.locator final.quotient final.degree := by
  obtain ⟨final, prior, balance, locLen, qLen, product, branch⟩ :=
    trace_residual_factorization trace locRoom qRoom
  cases branch with
  | success exhausted =>
    rw [exhausted] at product
    exact ⟨final, exhausted, by omega, locLen, qLen, product, rfl⟩
  | reject active invalid =>
    have root := supplied final.index prior active
    rw [product] at root
    change ((rootProduct roots index (final.index - index) * activeLocator final.locator final.degree).eval
      (toField roots[final.index]!.bv)) = 0 at root
    rw [eval_mul] at root
    exact False.elim (invalid ((mul_eq_zero.mp root).resolve_left
      (product_eval_ne_zero roots (final.index - index) index final.index (by omega) active distinct)))

/-- The exact source wrapper passes the residual of all distinct verified
candidate roots to Roots.start and returns the resulting stage. -/
def ActualNativeDeflateDistinct : Prop :=
  ∀ {K : Type} (field : bulksketch.field.BinaryField bulksketch.field.Gf64)
    (kernels : BulkKernels K bulksketch.field.Gf64)
    (_mul : ∀ a b, kernels.ArithmeticInst.mul a b = .ok (mulWord a b))
    (self : Execution bulksketch.field.Gf64 K) (input : RowInput)
    (workspace : RowWorkspace) (meter meter1 : WorkMeter),
    DeflateBounds self input workspace →
    self.degree.val < workspace.polynomials.length →
    StageCharge.chargeResult meter (deflateCost self.degree) = (.Ok (), meter1) →
    let width := input.difference.length + 1
    let roots := prefixSlice workspace.roots self.hits.val
    let locator := prefixSlice workspace.bm width
    let initial := activeLocator locator self.degree
    (∀ j, j < self.hits.val → initial.IsRoot (toField roots[j]!.bv)) →
    (∀ i j, i < j → j < self.hits.val → roots[i]! ≠ roots[j]!) →
    ∃ final : FinalState,
      final.index = self.hits.val ∧ final.degree.val + self.hits.val = self.degree.val ∧
      final.locator.length = width ∧ final.quotient.length = width ∧
      initial = rootProduct roots 0 self.hits.val * activeLocator final.locator final.degree ∧
      let updated := finishedRoots self.roots final.degree
      let joined := joinedWorkspace (deflateFrame self workspace width) final.locator final.quotient
      Execution.deflate field kernels self input workspace meter =
        .ok (.Ok (.Ok (some (ClosedLeafAdvance.stageFor updated))), {self with roots := updated},
          RootSetup.startedWorkspace final.degree joined, id, meter1)

theorem native_deflate_distinct : ActualNativeDeflateDistinct := by
  intro K field kernels mul self input workspace meter meter1 bounds polyRoom charged
  dsimp only
  intro supplied distinct
  have stage := native_deflate field kernels mul self input workspace meter (deflateCost self.degree)
    (deflate_price self.degree) (fun _ => bounds)
  rw [charged] at stage
  obtain ⟨result, trace, native⟩ := stage
  let width := input.difference.length + 1
  let roots := prefixSlice workspace.roots self.hits.val
  let locator := prefixSlice workspace.bm width
  let quotient := prefixSlice (BmEntry.tail workspace.bm width) width
  obtain ⟨bmRoom, degreeRoom, _, rootsRoom⟩ := bounds
  have rootLength : roots.length = self.hits.val := by
    change (prefixSlice workspace.roots self.hits.val).length = self.hits.val
    rw [prefix_length, Nat.min_eq_left rootsRoom]
  have locLength : locator.length = width := by
    change (prefixSlice workspace.bm width).length = width
    rw [prefix_length, Nat.min_eq_left (by omega)]
  have qLength : quotient.length = width := by
    change (prefixSlice (BmEntry.tail workspace.bm width) width).length = width
    rw [prefix_length, BmEntry.tail_length, Nat.min_eq_left (by omega)]
  obtain ⟨final, exhausted, degree, locLen, qLen, product, completed⟩ :=
    trace_distinct_candidates_success trace (by change self.degree.val < locator.length; omega)
      (by change self.degree.val ≤ quotient.length; omega)
      (fun j _ bound => supplied j (by change j < roots.length at bound; omega))
      (fun i j ordered bound => distinct i j ordered (by change j < roots.length at bound; omega))
  change final.index = roots.length at exhausted
  change final.degree.val + (roots.length - 0) = self.degree.val at degree
  change final.locator.length = locator.length at locLen
  change final.quotient.length = quotient.length at qLen
  rw [rootLength] at exhausted degree
  rw [locLength] at locLen
  rw [qLength] at qLen
  change activeLocator locator self.degree =
    rootProduct roots 0 (roots.length - 0) * activeLocator final.locator final.degree at product
  rw [rootLength, Nat.sub_zero] at product
  refine ⟨final, exhausted, by omega, locLen, qLen, product, ?_⟩
  let joined := joinedWorkspace (deflateFrame self workspace width) final.locator final.quotient
  have bmLen : joined.bm.length = workspace.bm.length :=
    BmEntry.splitBack_length workspace.bm width _
  have bmMax : workspace.bm.length ≤ Usize.max := Slice.length_ineq workspace.bm
  have startBounds : RootSetup.RootStartBounds final.degree joined :=
    ⟨by omega, fun _ => ⟨by change final.degree.val < workspace.polynomials.length; omega, by omega⟩⟩
  rw [native, completed, start_output_normal _ _ _ _ startBounds]
  simp only [wrapDeflate, bind_ok]
  dsimp! only
  rfl

#print axioms trace_residual_factorization
#print axioms trace_distinct_candidates_success
#print axioms native_deflate_distinct

end BulksketchBridge.Deflation
