import Arithmetic.AffineQuarticGenerated
import BulksketchBridge.CubicSpec
import BulksketchBridge.DirectTwoSpec
import BulksketchBridge.AffineQuarticAlgebra

namespace BulksketchBridge.AffineQuartic

open Aeneas.Std Algebra.Gf64 bulksketch.backend.contract

abbrev fieldDictionary := Cubic.fieldDictionary
abbrev mulWord := Inverse.multiplyNativeWord
abbrev squareWord := Square.expectedWord
noncomputable abbrev inverseWord := DirectTwo.inverseWord

def factorWords (b c : U64) : Slice U64 :=
  Array.to_slice (Array.make 4#usize [c, b, 0#u64, 1#u64])

def scratchWords : Slice U64 := Array.to_slice (Array.repeat 4#usize 0#u64)

noncomputable def evaluate (b c d : U64) (z : Field) : Field :=
  z ^ 4 + toField b.bv * z ^ 2 + toField c.bv * z + toField d.bv

/-- The native cubic call and native product certificate gate recovery.
The independent existence result is scoped to an accepted kernel. -/
def CertifiedKernel {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) (b c : U64) : Prop :=
  ∃ kernel : Array U64 3#usize, ∃ scratch : Slice U64,
    bulksketch.decode.deg34.cubic fieldDictionary kernels 0#u64 b c = .ok (some kernel) ∧
    bulksketch.decode.deg34.certificate fieldDictionary kernels (factorWords b c)
      (Array.to_slice kernel) scratchWords = .ok (true, scratch)

def FourRoots (b c d : U64) (roots : Array U64 4#usize) : Prop :=
  roots.val.Nodup ∧ ∀ word ∈ roots.val, evaluate b c d (toField word.bv) = 0

def scaledTarget (other inverse target : U64) : U64 :=
  mulWord target (squareWord (mulWord other inverse))

/-- The three normalized scalar quadratic choices after the kernel gate.
The four output words remain in the source order. -/
noncomputable def fiberChoices (u v c d : U64) : Option (Array U64 4#usize) := do
  let outer ← MapsQuadratic.expectedSolution (scaledTarget u (inverseWord c) d)
  let w := mulWord v outer
  let first ← MapsQuadratic.expectedSolution (scaledTarget v (inverseWord c) w)
  let second ← MapsQuadratic.expectedSolution (scaledTarget v (inverseWord c) (w ^^^ v))
  let x := mulWord u first
  let y := mulWord u second
  some (Array.make 4#usize [x, x ^^^ u, y, y ^^^ u])

/-- The exact native helper always returns normally. After the native kernel
gate it succeeds exactly when the supplied affine quartic has a root, and
every success gives four distinct roots. -/
def ActualAffineQuarticRefines : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) (b c d : U64),
    Cubic.CorrectArithmetic kernels →
    ∃ output, bulksketch.decode.deg34.affine_quartic fieldDictionary kernels b c d = .ok output ∧
      (∀ roots, output = some roots → FourRoots b c d roots) ∧
      ((∃ roots, output = some roots) ↔ c ≠ 0#u64 ∧ CertifiedKernel kernels b c ∧
        ∃ z : Field, evaluate b c d z = 0)

end BulksketchBridge.AffineQuartic
