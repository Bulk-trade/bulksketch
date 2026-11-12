import Arithmetic.QuarticGenerated
import BulksketchBridge.InverseFieldSpec

namespace BulksketchBridge.QuarticLoops

open Aeneas.Std
open bulksketch.backend.contract bulksketch.decode.deg34

abbrev Words := Array U64 4#usize
abbrev fieldDictionary := bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField
abbrev mulWord := Inverse.multiplyNativeWord
abbrev NativeMul {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) :=
  ∀ left right, kernels.ArithmeticInst.mul left right = bulksketch.field.gf64.mul fieldDictionary left right

/-- Exact products on the original initialized array, in source word order. -/
def prefixes (roots : Words) : Words :=
  let r0 := roots[0]!
  let r01 := mulWord r0 roots[1]!
  Array.make 4#usize [1#u64, r0, r01, mulWord r01 roots[2]!]

/-- Exact reverse write-back array. Each inverse update reads the original root word. -/
def shiftedReciprocals (roots prefixes : Words) (shift inverse : U64) : Words :=
  let i3 := mulWord inverse roots[3]!
  let i2 := mulWord i3 roots[2]!
  let i1 := mulWord i2 roots[1]!
  Array.make 4#usize [mulWord prefixes[0]! i1 ^^^ shift, mulWord prefixes[1]! i2 ^^^ shift,
    mulWord prefixes[2]! i3 ^^^ shift, mulWord prefixes[3]! inverse ^^^ shift]

/-- The original forward loop writes the three nonconstant prefix products. -/
def ActualQuarticPrefixProducts : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) (roots : Words),
    NativeMul kernels →
    quartic_loop0 fieldDictionary kernels ⟨1#usize, 4#usize⟩ roots (Array.repeat 4#usize 1#u64) =
      Result.ok (prefixes roots)

/-- The original reverse loop writes exactly the four shifted words for any prefix and initial inverse. -/
def ActualQuarticReverseWords : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) (roots prefixes : Words) (shift inverse : U64),
    NativeMul kernels →
    quartic_loop1 fieldDictionary kernels ⟨⟨0#usize, 4#usize⟩⟩ shift roots prefixes inverse =
      Result.ok (shiftedReciprocals roots prefixes shift inverse)

end BulksketchBridge.QuarticLoops
