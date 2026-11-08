import BulksketchBridge.BmTerminalSpec
import BulksketchBridge.StageChargeSpec
import BulksketchBridge.ClosedLeafAdvanceSpec

namespace BulksketchBridge.BmStepControl

open Aeneas.Std BmTerminal
open bulksketch.backend.contract bulksketch.decode.bm bulksketch.types

abbrev IndexRange := core.ops.range.Range Usize

/-- The wrapper paid for index zero before entering the loop. Every later
index performs a separate verified meter transition. -/
def stepCharge (index : Usize) (meter : WorkMeter) (cost : WorkUnits) : StageCharge.ChargeResult :=
  if index = 0#usize then (.Ok (), meter)
  else StageCharge.chargeResult meter (.Ok cost)

def incremented (value : Usize) : Usize :=
  ClosedLeafAdvance.usizeWord (value.val + 1)

def nextRange (iter : IndexRange) : IndexRange := ⟨incremented iter.start, iter.«end»⟩

/-- A failed later charge returns before the parity and discrepancy checks.
All three buffer frames rejoin with their current words. -/
def ActualBmChargeFailure : Prop :=
  ∀ {F K : Type} (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F)
    (back0 back1 back2 : Back) (tail syndromes : Slice U64) (budget : Usize) (cost : WorkUnits)
    (iter : IndexRange) (meter finalMeter : WorkMeter) (connection previous saved : Slice U64)
    (degree previousLen shift : Usize) (previousDelta : U64) (error : DecodeError),
    iter.start.val < iter.«end».val →
    stepCharge iter.start meter cost = (.Err error, finalMeter) →
    locator_loop0.body field kernels back0 back1 tail back2 syndromes budget cost iter meter
      connection previous saved degree previousLen shift previousDelta =
        .ok (.done (.Err error, joinBuffers back0 back1 back2 tail connection previous saved, finalMeter))

/-- A charged odd index has exact zero discrepancy in the source control
path. It advances the iterator and shift and passes through the current
three buffers, degree, previous length and previous discrepancy. -/
def ActualBmOddSkip : Prop :=
  ∀ {F K : Type} (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F)
    (back0 back1 back2 : Back) (tail syndromes : Slice U64) (budget : Usize) (cost : WorkUnits)
    (iter : IndexRange) (meter finalMeter : WorkMeter) (connection previous saved : Slice U64)
    (degree previousLen shift : Usize) (previousDelta : U64),
    iter.start.val < iter.«end».val → iter.start.val % 2 = 1 → shift.val + 1 ≤ Usize.max →
    stepCharge iter.start meter cost = (.Ok (), finalMeter) →
    locator_loop0.body field kernels back0 back1 tail back2 syndromes budget cost iter meter
      connection previous saved degree previousLen shift previousDelta =
        .ok (.cont (nextRange iter, finalMeter, connection, previous, saved,
          degree, previousLen, incremented shift, previousDelta))

end BulksketchBridge.BmStepControl
