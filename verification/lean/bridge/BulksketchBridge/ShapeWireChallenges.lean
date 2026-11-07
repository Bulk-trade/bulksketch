import Arithmetic.ShapeWireGenerated

namespace BulksketchBridge.ShapeWireChallenges

open Aeneas.Std

def payloadBytes (buckets words : Nat) : Nat := 8 * words + (buckets + 7) / 8

def wireBytes (buckets words : Nat) : Nat := 24 + 2 * buckets + payloadBytes buckets words

/-- Both wire lengths must fit in u32, and the complete record must fit in usize. -/
abbrev fits (buckets words : Nat) : Prop :=
  2 * buckets ≤ U32.max ∧ payloadBytes buckets words ≤ U32.max ∧
    wireBytes buckets words ≤ Usize.max

def expectedBytes (buckets words : Nat) : Option Nat :=
  if fits buckets words then some (wireBytes buckets words) else none

def actualRecordBytesMatchesWireBounds : Prop :=
  ∀ buckets words : Usize, ∃ output : Option Usize,
    bulksketch.sketch.shape.record_bytes buckets words = Result.ok output ∧
      output.map UScalar.val = expectedBytes buckets.val words.val

end BulksketchBridge.ShapeWireChallenges
