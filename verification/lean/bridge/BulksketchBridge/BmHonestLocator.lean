import BulksketchBridge.BmHonestLocatorSpec
import BulksketchBridge.BmLocatorResidual
import BulksketchBridge.BmEvenStep

namespace BulksketchBridge.BmHonestLocator

open Aeneas.Std BmLoop BmStepControl BmEvenStep BmDiscrepancy Algebra.Gf64
open bulksketch.backend.contract bulksketch.decode.bm bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem step_honest {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (raw : RawArithmetic kernels) (reduce : ReduceArithmetic kernels)
    (roots : Finset Field) (input : Input) (state : State)
    (noZero : (0 : Field) ∉ roots) (cardBound : roots.card ≤ input.budget.val)
    (ordered : state.1.start.val ≤ state.1.«end».val)
    (admitted : Admitted input state) (algebra : Algebraic input state)
    (degreeBound : (stateDegree state).val ≤ roots.card)
    (moments : Moments roots input.syndromes state.1.«end».val) :
    match step input state with
    | .done reply => Outcome roots input state reply
    | .cont next => (stateDegree next).val ≤ roots.card := by
  rcases state with ⟨iter, meter, connection, previous, saved, degree, previousLen, shift, scale⟩
  change iter.start.val ≤ iter.«end».val at ordered
  change degree.val ≤ roots.card at degreeBound
  change Moments roots input.syndromes iter.«end».val at moments
  change BmResidualInvariant.Invariant input.syndromes connection previous iter.start.val
    degree.val previousLen.val shift.val scale at algebra
  obtain ⟨budgetEnd, syndromeRoom, connectionRoom, previousRoom, savedRoom, scalar⟩ := admitted
  have degreeIndex := scalar.degreeIndex
  by_cases exhausted : iter.«end».val ≤ iter.start.val
  · have finished : iter.start.val = iter.«end».val := by omega
    have finalMoments : Moments roots input.syndromes iter.start.val := finished ▸ moments
    have degreeRoom : degree.val < connection.length := by omega
    have ⟨_, exactDegree, leading⟩ := BmSupportBounds.exact_terminal_degree roots input.syndromes connection
      previous iter.start.val degree.val previousLen.val shift.val scale algebra noZero degreeBound
      (by omega) (by omega) finalMoments
    have locator := BmSupportBounds.exact_normalized_locator roots input.syndromes connection previous
      iter.start.val degree.val previousLen.val shift.val scale algebra noZero degreeBound
      (by omega) (by omega) degreeRoom finalMoments
    simp only [step, exhausted, ite_true, BmTerminal.terminalResult, leading, algebra.constant,
      or_self, ite_false, Outcome]
    exact Or.inr ⟨finished, exactDegree, locator, rfl⟩
  have active : iter.start.val < iter.«end».val := by omega
  cases charged : stepCharge iter.start meter input.cost with
  | mk payment finalMeter =>
    cases payment with
    | Err error =>
      simp only [step, exhausted, ite_false, charged, Outcome]
      exact Or.inl ⟨error, finalMeter, active, rfl, rfl⟩
    | Ok paidUnit =>
      cases paidUnit
      by_cases even : iter.start.val % 2 = 0
      · by_cases zero : deltaWord connection input.syndromes degree iter.start = 0#u64
        · simpa only [step, exhausted, ite_false, charged, even, ite_true, zero, stateDegree] using degreeBound
        have prelude : PreludeBounds connection input.syndromes degree iter.start :=
          ⟨by omega, by omega, by omega⟩
        have current := BmCurrentDiscrepancy.current_discrepancy kernels raw reduce
          connection input.syndromes degree iter.start prelude degreeIndex
        have bounded : nextDegree degree iter.start ≤ roots.card :=
          BmSupportBounds.native_candidate_bound roots input.syndromes connection previous
            iter.start.val degree.val previousLen.val shift.val iter.«end».val scale
            (deltaWord connection input.syndromes degree iter.start) algebra degreeBound
            (by omega) syndromeRoom moments current zero
        have within : ¬ input.budget.val < nextDegree degree iter.start := by omega
        have max : input.syndromes.length ≤ Usize.max := input.syndromes.length_ineq
        have candidateVal := ClosedLeafAdvance.word_val (nextDegree degree iter.start) (by omega)
        simp only [step, exhausted, ite_false, charged, even, ite_true, zero, within,
          BmAccepted.expectedAccepted]
        by_cases grows : 2 * degree.val ≤ iter.start.val
        · simpa only [grows, ite_true, stateDegree, candidateVal] using bounded
        · simpa only [grows, ite_false, stateDegree] using degreeBound
      · simpa only [step, exhausted, ite_false, charged, even, eq_self, ite_true, stateDegree] using degreeBound

theorem run_honest {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (raw : RawArithmetic kernels) (reduce : ReduceArithmetic kernels)
    (roots : Finset Field) (input : Input) (state last : State) (reply : BmTerminal.Return) (fuel : Nat)
    (difference initial : Slice U64) (processed : Nat)
    (reconstructed : Reconstruction.Prefix difference initial input.syndromes processed)
    (noZero : (0 : Field) ∉ roots) (cardBound : roots.card ≤ input.budget.val)
    (ordered : state.1.start.val ≤ state.1.«end».val) (processedBound : state.1.«end».val < processed)
    (admitted : Admitted input state) (algebra : Algebraic input state)
    (degreeBound : (stateDegree state).val ≤ roots.card)
    (moments : Moments roots input.syndromes state.1.«end».val)
    (returned : run input fuel state = some (last, reply)) :
    Outcome roots input last reply := by
  induction fuel generalizing state with
  | zero =>
    cases taken : step input state with
    | done result =>
      have honest : Outcome roots input state result := by
        simpa only [taken] using step_honest kernels raw reduce roots input state noZero cardBound
          ordered admitted algebra degreeBound moments
      rw [run, taken] at returned
      cases returned
      exact honest
    | cont next =>
      rw [run, taken] at returned
      cases returned
  | succ fuel ih =>
    cases taken : step input state with
    | done result =>
      have honest : Outcome roots input state result := by
        simpa only [taken] using step_honest kernels raw reduce roots input state noZero cardBound
          ordered admitted algebra degreeBound moments
      rw [run, taken] at returned
      cases returned
      exact honest
    | cont next =>
      rw [run, taken] at returned
      obtain ⟨valid, index, sameEnd⟩ := advances input state next admitted taken
      have nextOrdered : next.1.start.val ≤ next.1.«end».val := by
        have active : state.1.start.val + 1 ≤ state.1.«end».val := by
          by_contra notActive
          rcases state with ⟨iter, meter, connection, previous, saved, degree, previousLen, shift, scale⟩
          change ¬ iter.start.val + 1 ≤ iter.«end».val at notActive
          simp only [step, show iter.«end».val ≤ iter.start.val by omega, ite_true] at taken
          cases taken
        rw [index, sameEnd]
        exact active
      have alg := algebraic_step kernels raw reduce input state next difference initial processed
        reconstructed processedBound admitted algebra taken
      have nextDegree : (stateDegree next).val ≤ roots.card := by
        simpa only [taken] using step_honest kernels raw reduce roots input state noZero cardBound
          ordered admitted algebra degreeBound moments
      exact ih next nextOrdered (sameEnd ▸ processedBound) valid alg nextDegree
        (sameEnd ▸ moments) returned

theorem honest_locator_refines : ActualHonestLocator := by
  intro K kernels raw reduce mul inverse roots syndromes buffers difference initialSyndromes capacity budget meter
    noZero cardBound budgetBound bufferBound syndromeBound reconstructed moments
  cases priced : BmEntry.pricing meter budget with
  | mk payment finalMeter =>
    cases payment with
    | Err error =>
      obtain ⟨reply, resultEq, native⟩ := BmLocator.locator_refines kernels raw reduce mul inverse
        syndromes capacity budget buffers meter (fun _ => ⟨budgetBound, bufferBound, syndromeBound⟩)
      simp only [BmLocator.result, priced, Option.some.injEq] at resultEq
      subst reply
      exact ⟨_, native, Or.inl ⟨error, finalMeter, rfl, rfl⟩⟩
    | Ok paidUnit =>
      cases paidUnit
      obtain ⟨last, reply, modeled, native, _⟩ := BmLocator.reconstructed_locator_refines
        kernels raw reduce mul inverse syndromes buffers difference initialSyndromes capacity budget meter finalMeter
        budgetBound bufferBound syndromeBound reconstructed priced
      let input := BmLocator.inputs syndromes buffers capacity budget
      let start := BmLocator.initial buffers capacity budget finalMeter
      have inputMax : syndromes.length ≤ Usize.max := syndromes.length_ineq
      have endVal : start.1.«end».val = 2 * capacity.val :=
        ClosedLeafAdvance.word_val _ (by omega)
      have startVal : start.1.start.val = 0 := by simp [start, BmLocator.initial]
      have valid : Admitted input start := BmLocator.initial_admitted syndromes buffers capacity budget
        finalMeter budgetBound bufferBound syndromeBound
      have alg : Algebraic input start := BmLocator.initial_algebraic syndromes buffers capacity budget
        finalMeter bufferBound
      have degreeBound : (stateDegree start).val ≤ roots.card := by simp [stateDegree, start, BmLocator.initial]
      have honest := run_honest kernels raw reduce roots input start last reply (2 * capacity.val)
        difference initialSyndromes (2 * capacity.val + 1) reconstructed noZero cardBound
        (by rw [startVal]; omega) (by rw [endVal]; omega) valid alg degreeBound (endVal ▸ moments) modeled
      exact ⟨reply, native, Or.inr ⟨finalMeter, last, rfl, modeled, honest⟩⟩

end BulksketchBridge.BmHonestLocator
