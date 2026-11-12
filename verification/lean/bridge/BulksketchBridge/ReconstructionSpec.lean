import Arithmetic.ReconstructionGenerated
import BulksketchProofs.Field.PeriodSpec

namespace BulksketchBridge.Reconstruction

open Aeneas.Std bulksketch.backend.contract

abbrev Inclusive := core.ops.range.RangeInclusive Usize

def squareWord (word : U64) : U64 :=
  ⟨BulksketchProofs.Field.Period.squareWord word.bv⟩

def SyndromeStep (difference syndromes : Slice U64) (index : Nat) : U64 :=
  if index % 2 = 0 then squareWord syndromes.val[index / 2]!
  else difference.val[index / 2]!

/-- Index zero is a sentinel. Positive coefficients obey the recurrence up to
the processed index. The remainder of the original scratch is untouched. -/
structure Prefix (difference initial syndromes : Slice U64) (processed : Nat) : Prop where
  length : syndromes.length = initial.length
  sentinel : syndromes.val[0]! = 0#u64
  recurrence : ∀ index, 0 < index → index < processed →
    syndromes.val[index]! = SyndromeStep difference syndromes index
  frame : ∀ index, processed ≤ index → index < initial.length →
    syndromes.val[index]! = initial.val[index]!

def processed (range : Inclusive) : Nat :=
  if range.exhausted then range.«end».val + 1 else range.start.val

def LoopContract (body : ∀ {F K : Type}, bulksketch.field.BinaryField F →
    BulkKernels K F → Inclusive → Slice U64 → Slice U64 → Aeneas.Std.Result (Slice U64)) : Prop :=
  ∀ {F K : Type} (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F)
    (range : Inclusive) (difference initial syndromes : Slice U64),
    (∀ word, kernels.ArithmeticInst.square word = .ok (squareWord word)) →
    1 ≤ range.start.val → range.start.val ≤ range.«end».val + 1 →
    range.«end».val = 2 * difference.length → range.«end».val < initial.length →
    Prefix difference initial syndromes (processed range) →
    ∃ final, body field kernels range difference syndromes = .ok final ∧
      Prefix difference initial final (2 * difference.length + 1)

def ActualReconstructionLoop0 : Prop := LoopContract bulksketch.decode.stages.Execution.reconstruct_loop0

def ActualReconstructionLoop1 : Prop := LoopContract bulksketch.decode.stages.Execution.reconstruct_loop1

end BulksketchBridge.Reconstruction
