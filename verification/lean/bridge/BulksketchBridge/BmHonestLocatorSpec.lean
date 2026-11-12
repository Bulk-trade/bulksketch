import BulksketchBridge.BmLocatorResidualSpec
import BulksketchBridge.BmSupportBounds

namespace BulksketchBridge.BmHonestLocator

open Aeneas.Std BmLoop Algebra.Gf64
open bulksketch.backend.contract bulksketch.decode.bm bulksketch.types

def Moments (roots : Finset Field) (syndromes : Slice U64) (observed : Nat) : Prop :=
  ∀ i, 0 < i → i ≤ observed → toField syndromes[i]!.bv = Reconciliation.powerSum roots i

def stateDegree : State → Usize
  | (_, _, _, _, _, degree, _, _, _) => degree

/-- A run on the positive moments of an admitted support can stop only
at a charge failure or at the original normalized terminal writeback.
The error branch retains the exact charge and scratch state. -/
def Outcome (roots : Finset Field) (input : Input) : State → BmTerminal.Return → Prop
  | (iter, meter, connection, previous, saved, degree, _, _, _), reply =>
    (∃ error finalMeter, iter.start.val < iter.«end».val ∧
      BmStepControl.stepCharge iter.start meter input.cost = (.Err error, finalMeter) ∧
      reply = finish input connection previous saved finalMeter (.Err error)) ∨
    (iter.start.val = iter.«end».val ∧ degree.val = roots.card ∧
      BmSyndromePolynomials.connectionPolynomial (BmTerminal.normalizedConnection connection degree.val)
        degree.val = Reconciliation.supportLocator roots ∧
      reply = finish input (BmTerminal.normalizedConnection connection degree.val)
        previous saved meter (.Ok (.Ok degree)))

/-- Native Berlekamp–Massey returns the exact monic support locator,
or an exact failure to price or charge one of its iterations. -/
def ActualHonestLocator : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    BmDiscrepancy.RawArithmetic kernels → BmDiscrepancy.ReduceArithmetic kernels →
    BmMutable.NativeMul kernels → BmTerminal.NativeInverse kernels →
    ∀ (roots : Finset Field) (syndromes buffers difference initialSyndromes : Slice U64)
      (capacity budget : Usize) (meter : WorkMeter),
      (0 : Field) ∉ roots → roots.card ≤ budget.val → budget.val ≤ capacity.val →
      3 * (capacity.val + 1) ≤ buffers.length → 2 * capacity.val + 1 ≤ syndromes.length →
      Reconstruction.Prefix difference initialSyndromes syndromes (2 * capacity.val + 1) →
      Moments roots syndromes (2 * capacity.val) →
      ∃ reply, locator BmEntry.fieldDictionary kernels syndromes capacity budget buffers meter = .ok reply ∧
        ((∃ error finalMeter, BmEntry.pricing meter budget = (.Err error, finalMeter) ∧
          reply = (.Err error, buffers, finalMeter)) ∨
        (∃ finalMeter last, BmEntry.pricing meter budget = (.Ok (), finalMeter) ∧
          let input := BmLocator.inputs syndromes buffers capacity budget
          let start := BmLocator.initial buffers capacity budget finalMeter
          run input (2 * capacity.val) start = some (last, reply) ∧ Outcome roots input last reply))

end BulksketchBridge.BmHonestLocator
