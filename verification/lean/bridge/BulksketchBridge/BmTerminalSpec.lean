import BulksketchBridge.BmMutableSpec
import BulksketchBridge.DirectTwoSpec
import BulksketchBridge.RebuiltLfsrSpec

namespace BulksketchBridge.BmTerminal

open Aeneas.Std DenseCoefficient RebuiltLfsr
open bulksketch.backend.contract bulksketch.decode.bm bulksketch.types

abbrev fieldDictionary := BmMutable.fieldDictionary
abbrev mulWord := Inverse.multiplyNativeWord
noncomputable abbrev inverseWord := DirectTwo.inverseWord
abbrev Back := Slice U64 × Slice U64 → Slice U64
abbrev Reply := core.result.Result (core.result.Result Usize DecodeFailure) DecodeError
abbrev Return := Reply × Slice U64 × WorkMeter

def NativeInverse {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) : Prop :=
  ∀ word, kernels.ArithmeticInst.inverse word =
    bulksketch.field.maps.inverse fieldDictionary word

def joinBuffers (back0 back1 back2 : Back) (tail connection previous saved : Slice U64) : Slice U64 :=
  back0 (connection, back1 (previous, back2 (saved, tail)))

def scaledPrefix (connection : Slice U64) (degree : Nat) (scale : U64) : Slice U64 :=
  Slice.from ((connection.val.take (degree + 1)).map (fun word => mulWord word scale))
    (by simp only [List.length_map, List.length_take]
        exact (Nat.min_le_right _ _).trans connection.length_ineq)

noncomputable def normalizedConnection (connection : Slice U64) (degree : Nat) : Slice U64 :=
  let scaled := scaledPrefix connection degree (inverseWord connection[0]!)
  restorePrefix connection (Slice.from scaled.val.reverse (by simpa using scaled.length_ineq))

/-- The native terminal check rejects a zero leading or constant word.
Success scales and reverses the admitted prefix and applies all three
original slice continuations. Both outcomes retain the input meter. -/
noncomputable def terminalResult (back0 back1 back2 : Back)
    (tail connection previous saved : Slice U64) (degree : Usize) (meter : WorkMeter) : Return :=
  if connection[degree.val]! = 0#u64 ∨ connection[0]! = 0#u64 then
    (.Ok (.Err .InvalidLocator), joinBuffers back0 back1 back2 tail connection previous saved, meter)
  else
    (.Ok (.Ok degree),
      joinBuffers back0 back1 back2 tail (normalizedConnection connection degree.val) previous saved, meter)

def ActualBmTerminalBody : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64), BmMutable.NativeMul kernels →
    NativeInverse kernels →
    ∀ (back0 back1 back2 : Back) (tail syndromes : Slice U64) (budget : Usize) (cost : WorkUnits)
      (iter : core.ops.range.Range Usize) (meter : WorkMeter) (connection previous saved : Slice U64)
      (degree previousLen shift : Usize) (previousDelta : U64),
      iter.«end».val ≤ iter.start.val → degree.val < connection.length →
      locator_loop0.body fieldDictionary kernels back0 back1 tail back2 syndromes budget cost iter meter
        connection previous saved degree previousLen shift previousDelta =
          .ok (.done (terminalResult back0 back1 back2 tail connection previous saved degree meter))

def ActualBmTerminalLoop : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64), BmMutable.NativeMul kernels →
    NativeInverse kernels →
    ∀ (back0 back1 back2 : Back) (tail syndromes : Slice U64) (budget : Usize) (cost : WorkUnits)
      (iter : core.ops.range.Range Usize) (meter : WorkMeter) (connection previous saved : Slice U64)
      (degree previousLen shift : Usize) (previousDelta : U64),
      iter.«end».val ≤ iter.start.val → degree.val < connection.length →
      locator_loop0 fieldDictionary kernels back0 back1 tail back2 iter syndromes budget meter cost
        connection previous saved degree previousLen shift previousDelta =
          .ok (terminalResult back0 back1 back2 tail connection previous saved degree meter)

end BulksketchBridge.BmTerminal
