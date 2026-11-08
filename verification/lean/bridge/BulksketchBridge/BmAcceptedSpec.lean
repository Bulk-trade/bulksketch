import BulksketchBridge.BmEvenStepSpec
import BulksketchBridge.BmConnectionUpdate

namespace BulksketchBridge.BmAccepted

open Aeneas Aeneas.Std BmDiscrepancy BmStepControl BmEvenStep DenseCoefficient RebuiltLfsr
open bulksketch.backend.contract bulksketch.decode.bm bulksketch.types

/-- The slice prefix copy shared by both original growth branches.
   The saved-prefix update applies the same sequence to the previous row. -/
def copyPrefix (destination source : Slice U64) (len : Usize) : Result (Slice U64) := do
  let (head, back) ← core.slice.index.Slice.index_mut
    (core.slice.index.SliceIndexRangeToUsizeSlice U64) destination { «end» := len }
  let input ← core.slice.index.Slice.index
    (core.slice.index.SliceIndexRangeToUsizeSlice U64) source { «end» := len }
  let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU64 head input
  .ok (back copied)

abbrev Cont := IndexRange × WorkMeter × Slice U64 × Slice U64 × Slice U64 × Usize × Usize × Usize × U64
abbrev BodyResult := Result (ControlFlow Cont BmTerminal.Return)

def acceptedTail {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (next : IndexRange) (meter : WorkMeter) (connection previous saved : Slice U64)
    (degree candidate previousLen shift : Usize) (previousDelta delta : U64) (grows : Prop)
    [Decidable grows] : BodyResult := do
  let len ← degree + 1#usize
  let saved1 ← if grows then copyPrefix saved connection len else .ok saved
  let connection1 ← BmConnectionUpdate.run kernels connection previous len candidate shift previousLen previousDelta delta
  if grows then
    let previous1 ← copyPrefix previous saved1 len
    .ok (.cont (next, meter, connection1, previous1, saved1, candidate, len, 1#usize, delta))
  else
    let shift1 ← shift + 1#usize
    .ok (.cont (next, meter, connection1, previous, saved1, degree, previousLen, shift1, previousDelta))

structure UpdateBounds (connection previous saved : Slice U64)
    (degree index shift previousLen : Usize) : Prop where
  candidate : nextDegree degree index < connection.length
  shifted : shift.val + previousLen.val ≤ connection.length
  previousRead : previousLen.val ≤ previous.length
  growthCopies : 2 * degree.val ≤ index.val →
    degree.val + 1 ≤ previous.length ∧ degree.val + 1 ≤ saved.length
  incrementShift : ¬ 2 * degree.val ≤ index.val → shift.val + 1 ≤ Usize.max

/-- Accepted outer step with the exact updated connection and growth frames. -/
def expectedAccepted (next : IndexRange) (meter : WorkMeter) (connection previous saved : Slice U64)
    (degree candidate len previousLen shift : Usize) (previousDelta delta : U64) (grows : Prop)
    [Decidable grows] : Cont :=
  let updated := BmConnectionUpdate.expectedConnection connection previous len.val candidate.val
    shift.val previousLen.val previousDelta delta
  if grows then
    let old := (DenseCoefficient.prefixSlice connection len.val).val
    (next, meter, updated, previous.setSlice! 0 old, saved.setSlice! 0 old, candidate, len, 1#usize, delta)
  else
    (next, meter, updated, previous, saved, degree, previousLen, incremented shift, previousDelta)

def ActualBmAcceptedUpdate : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (raw : RawArithmetic kernels) (reduce : ReduceArithmetic kernels) (mul : BmMutable.NativeMul kernels)
    (back0 back1 back2 : BmTerminal.Back) (tail syndromes : Slice U64)
    (budget : Usize) (cost : WorkUnits) (iter : IndexRange) (meter finalMeter : WorkMeter)
    (connection previous saved : Slice U64) (degree previousLen shift : Usize) (previousDelta : U64)
    (active : iter.start.val < iter.«end».val) (even : iter.start.val % 2 = 0)
    (bounds : PreludeBounds connection syndromes degree iter.start)
    (charged : stepCharge iter.start meter cost = (.Ok (), finalMeter))
    (nonzero : deltaWord connection syndromes degree iter.start ≠ 0#u64)
    (twiceFits : 2 * degree.val ≤ Usize.max) (within : nextDegree degree iter.start ≤ budget.val)
    (updateBounds : UpdateBounds connection previous saved degree iter.start shift previousLen),
    ∃ candidate len : Usize, candidate.val = nextDegree degree iter.start ∧ len.val = degree.val + 1 ∧
      locator_loop0.body fieldDictionary kernels back0 back1 tail back2 syndromes budget cost iter meter
        connection previous saved degree previousLen shift previousDelta =
      .ok (.cont (expectedAccepted (nextRange iter) finalMeter connection previous saved degree candidate len
        previousLen shift previousDelta (deltaWord connection syndromes degree iter.start)
        (2 * degree.val ≤ iter.start.val)))

end BulksketchBridge.BmAccepted
