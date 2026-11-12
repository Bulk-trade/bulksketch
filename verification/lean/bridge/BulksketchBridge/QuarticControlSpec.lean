import BulksketchBridge.QuarticLoopSpec
import BulksketchBridge.AffineQuarticSpec

namespace BulksketchBridge.QuarticControl

open Aeneas.Std bulksketch.backend.contract bulksketch.decode.deg34

abbrev Words := QuarticLoops.Words
abbrev fieldDictionary := Cubic.fieldDictionary
abbrev mulWord := Inverse.multiplyNativeWord
abbrev squareWord := Square.expectedWord
abbrev frobeniusWord := Inverse.frobeniusNativeWord
noncomputable abbrev inverseWord := DirectTwo.inverseWord

/-- The two 31-step Frobenius calls followed by the final square. -/
def shiftWord (ratio : U64) : U64 :=
  squareWord (frobeniusWord (frobeniusWord ratio 31#u32) 31#u32)

def denominatorWord (b d shift : U64) : U64 :=
  squareWord (squareWord shift) ^^^ mulWord b (squareWord shift) ^^^ d

def transformedCoefficients (a b shift inverseDenominator : U64) : U64 × U64 × U64 :=
  (mulWord (b ^^^ mulWord a shift) inverseDenominator, mulWord a inverseDenominator,
    inverseDenominator)

inductive AffineCall where
  | direct (b c d : U64)
  | shifted (b c d shift : U64)

/-- The affine call chosen by the original coefficient and denominator guards. -/
noncomputable def prepare (a b c d : U64) : Option AffineCall :=
  if a = 0#u64 then some (.direct b c d) else
    let shift := shiftWord (mulWord c (inverseWord a))
    let denominator := denominatorWord b d shift
    if denominator = 0#u64 then none else
      let (b', c', d') := transformedCoefficients a b shift (inverseWord denominator)
      some (.shifted b' c' d' shift)

/-- Exact checked batch inverse and reverse write-back after the shifted affine call. -/
noncomputable def finish (shift : U64) (output : Option Words) : Option Words := do
  let roots ← output
  if 0#u64 ∈ roots.val then none else do
    let prefixes := QuarticLoops.prefixes roots
    let inverse ← Inverse.expectedFieldInverse (mulWord prefixes[3]! roots[3]!)
    some (QuarticLoops.shiftedReciprocals roots prefixes shift inverse)

/-- A per-call affine output witness ties the outer control equation to the
already verified affine body. -/
def ActualQuarticReturnsExact : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) (factor : Slice U64),
    Cubic.CorrectArithmetic kernels → 4 ≤ factor.length →
    match prepare factor[3]! factor[2]! factor[1]! factor[0]! with
    | none => quartic fieldDictionary kernels factor = Result.ok none
    | some (.direct b c d) => ∃ output,
        affine_quartic fieldDictionary kernels b c d = Result.ok output ∧
        quartic fieldDictionary kernels factor = Result.ok output
    | some (.shifted b c d shift) => ∃ output,
        affine_quartic fieldDictionary kernels b c d = Result.ok output ∧
        quartic fieldDictionary kernels factor = Result.ok (finish shift output)

end BulksketchBridge.QuarticControl
