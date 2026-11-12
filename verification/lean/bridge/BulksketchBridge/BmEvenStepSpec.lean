import BulksketchBridge.BmDiscrepancySpec
import BulksketchBridge.BmStepControlSpec

namespace BulksketchBridge.BmEvenStep

open Aeneas.Std BmDiscrepancy BmStepControl
open bulksketch.backend.contract bulksketch.decode.bm bulksketch.types

structure PreludeBounds (connection syndromes : Slice U64) (degree index : Usize) : Prop where
  connection : degree.val < connection.length
  lower : degree.val ≤ index.val + 1
  syndromes : index.val + 1 < syndromes.length

def rawDelta (connection syndromes : Slice U64) (degree index : Usize) : Raw :=
  let state := sourceZip connection syndromes degree.val index.val
  rawFold (remainingPairs state.fst.slice state.snd.iter.slice 0) ⟨0#u64, 0#u64⟩

def deltaWord (connection syndromes : Slice U64) (degree index : Usize) : U64 :=
  let raw := rawDelta connection syndromes degree index
  ⟨BulksketchProofs.Field.reduceFold64 raw.lo.bv raw.hi.bv⟩

def nextDegree (degree index : Usize) : Nat :=
  if 2 * degree.val ≤ index.val then index.val + 1 - degree.val else degree.val

def ActualBmEvenZero : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    RawArithmetic kernels → ReduceArithmetic kernels →
    ∀ (back0 back1 back2 : BmTerminal.Back) (tail syndromes : Slice U64)
      (budget : Usize) (cost : WorkUnits) (iter : IndexRange) (meter finalMeter : WorkMeter)
      (connection previous saved : Slice U64) (degree previousLen shift : Usize) (previousDelta : U64),
      iter.start.val < iter.«end».val → iter.start.val % 2 = 0 →
      PreludeBounds connection syndromes degree iter.start →
      stepCharge iter.start meter cost = (.Ok (), finalMeter) →
      deltaWord connection syndromes degree iter.start = 0#u64 → shift.val + 1 ≤ Usize.max →
      locator_loop0.body fieldDictionary kernels back0 back1 tail back2 syndromes budget cost iter meter
        connection previous saved degree previousLen shift previousDelta =
        .ok (.cont (nextRange iter, finalMeter, connection, previous, saved,
          degree, previousLen, incremented shift, previousDelta))

def ActualBmDegreeExceedsBudget : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    RawArithmetic kernels → ReduceArithmetic kernels →
    ∀ (back0 back1 back2 : BmTerminal.Back) (tail syndromes : Slice U64)
      (budget : Usize) (cost : WorkUnits) (iter : IndexRange) (meter finalMeter : WorkMeter)
      (connection previous saved : Slice U64) (degree previousLen shift : Usize) (previousDelta : U64),
      iter.start.val < iter.«end».val → iter.start.val % 2 = 0 →
      PreludeBounds connection syndromes degree iter.start →
      stepCharge iter.start meter cost = (.Ok (), finalMeter) →
      deltaWord connection syndromes degree iter.start ≠ 0#u64 →
      2 * degree.val ≤ Usize.max → budget.val < nextDegree degree iter.start →
      locator_loop0.body fieldDictionary kernels back0 back1 tail back2 syndromes budget cost iter meter
        connection previous saved degree previousLen shift previousDelta =
        .ok (.done (.Ok (.Err .DegreeExceedsBudget),
          BmTerminal.joinBuffers back0 back1 back2 tail connection previous saved, finalMeter))

end BulksketchBridge.BmEvenStep
