import BulksketchBridge.DegreeProbeRuntimeRunSpec

namespace BulksketchBridge.ProbeVerification

open Aeneas.Std DegreeProbeRuntime DenseCoefficient RebuiltLfsr
open bulksketch.backend.contract

def precheckRejects (odd roots : Slice U64) : Bool :=
  decide (roots.length ≤ 2) &&
    ((PortableEncoding.foldColumn roots.val 0 0#u64 != odd[0]!) ||
      (decide (2 ≤ odd.length) && (PortableEncoding.foldColumn roots.val 1 0#u64 != odd[1]!)))

/-- The short-root checks precede any access to the mutable verification window.
If they pass, the full encoder must agree with every word in the input row. -/
def expected (odd roots scratch : Slice U64) : Bool × Slice U64 :=
  if precheckRejects odd roots then (false, scratch)
  else
    let words := encodedWords (prefixSlice scratch odd.length) roots
    (decide (words = odd), restorePrefix scratch words)

structure Bounds (odd roots scratch : Slice U64) : Prop where
  firstRead : roots.length ≤ 2 → 0 < odd.length
  encodingWindow : precheckRejects odd roots = false → odd.length ≤ scratch.length

/-- The original verifier covers both short-circuit reads and full encoding.
Callback equations name the exact native arithmetic and the independent encoder model. -/
def ActualProbeVerified : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    (∀ x y, kernels.ArithmeticInst.mul x y = bulksketch.field.gf64.mul fieldDictionary x y) →
    (∀ x, kernels.ArithmeticInst.square x = bulksketch.field.gf64.square fieldDictionary x) →
    CorrectEncoding kernels →
    ∀ odd roots scratch, Bounds odd roots scratch →
      bulksketch.decode.probe.verified fieldDictionary kernels odd roots scratch =
        .ok (expected odd roots scratch)

end BulksketchBridge.ProbeVerification
