import BulksketchBridge.CertificateLoop

namespace BulksketchBridge.Certificate

open Aeneas.Std RebuiltLfsr DenseCoefficient

/-- In GF64 every word fits the field mask. The remaining two root rejections
are zero and a duplicate in the already inspected prefix. -/
def invalidAt (roots : Slice U64) (index : Nat) : Prop :=
  roots[index]! = 0#u64 ∨ roots[index]! ∈ roots.val.take index

instance (roots : Slice U64) (index : Nat) : Decidable (invalidAt roots index) :=
  inferInstanceAs (Decidable (_ ∨ _))

def invalidFrom (roots : Slice U64) (index : Nat) : Nat → Bool
  | 0 => false
  | remaining + 1 => decide (invalidAt roots index) || invalidFrom roots (index + 1) remaining

def rebuiltProduct (roots shape : Slice U64) : Slice U64 :=
  productFrom roots ((zeroWords shape).setAtNat 0 1#u64) 0 roots.length

def expected (factor roots scratch : Slice U64) : Bool × Slice U64 :=
  if roots.length + 1 ≠ factor.length ∨ invalidFrom roots 0 roots.length then (false, scratch)
  else
    let output := rebuiltProduct roots (prefixSlice scratch factor.length)
    (decide (output = factor), restorePrefix scratch output)

/-- The original native certificate computes the exact acceptance bit and
scratch frame, including both early rejections. The scratch capacity is
required only on paths that reach the mutable prefix. -/
def ActualCertificateReturnsExactFrame : Prop :=
  ∀ {K : Type} (kernels : bulksketch.backend.contract.BulkKernels K bulksketch.field.Gf64),
    NativeMul kernels → ∀ (factor roots scratch : Slice U64),
    roots.length + 1 ≤ Usize.max →
    (roots.length + 1 = factor.length → invalidFrom roots 0 roots.length = false →
      factor.length ≤ scratch.length) →
    bulksketch.decode.deg34.certificate fieldDictionary kernels factor roots scratch =
      Result.ok (expected factor roots scratch)

end BulksketchBridge.Certificate
