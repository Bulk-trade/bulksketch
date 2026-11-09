import Arithmetic.AffineMultipleGenerated
import BulksketchBridge.PortableZipMap
import BulksketchBridge.DenseDivRemControl

namespace BulksketchBridge.AffineMultiple

open Aeneas Aeneas.Std Result ControlFlow
open BulksketchBridge BulksketchBridge.MutableZip
open bulksketch.backend.contract bulksketch.decode.affine

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

abbrev Zip := State U64 U64
abbrev Back := Zip → Zip
abbrev Body := Zip × Back → Result (ControlFlow (Zip × Back) (Zip × Back))
abbrev dictionary := bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField

def scaleWord (inverse : U64) (_old value : U64) : U64 :=
  Inverse.multiplyNativeWord value inverse

private theorem apply_step_at (raw : Slice U64) (right : Slice U64)
    (f : U64 → U64 → U64) (i cursor : Nat) (active : i < raw.length) :
    replaceLeft (stateAt (mapFrom raw right f (i + 1)) right cursor)
        i (f raw[i]! right[i]!) =
      stateAt (mapFrom raw right f i) right cursor := by
  have same := congrArg (fun (z : Zip) => z.fst.slice) (apply_step raw right f i active)
  change (mapFrom raw right f (i + 1)).setAtNat i (f raw[i]! right[i]!) = mapFrom raw right f i at same
  simp only [replaceLeft, stateAt, same]

private theorem zip_fold (body : Body) (raw : Slice U64) (right : Slice U64)
    (f : U64 → U64 → U64)
    (activeBody : ∀ start < raw.length, ∀ back : Back,
      body (stateAt raw right start, back) =
        .ok (.cont (stateAt raw right (start + 1), fun final =>
          back (replaceLeft final start (f raw[start]! right[start]!)))))
    (stopBody : ∀ back : Back,
      body (stateAt raw right raw.length, back) = .ok (.done (stateAt raw right raw.length, back))) :
    ∀ start ≤ raw.length, ∀ back : Back,
      ∃ restore, loop body (stateAt raw right start, back) = .ok (stateAt raw right raw.length, restore) ∧
        ∀ cursor, restore (stateAt raw right cursor) =
          back (stateAt (mapFrom raw right f start) right cursor) := by
  suffices ∀ remaining start, start ≤ raw.length → raw.length - start = remaining →
      ∀ back : Back, ∃ restore, loop body (stateAt raw right start, back) = .ok (stateAt raw right raw.length, restore) ∧
        ∀ cursor, restore (stateAt raw right cursor) =
          back (stateAt (mapFrom raw right f start) right cursor) by
    intro start bound back
    exact this (raw.length - start) start bound rfl back
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
    intro start bound exactRemaining back
    by_cases active : start < raw.length
    · obtain ⟨restore, eq, applied⟩ :=
        ih (raw.length - (start + 1)) (by omega) (start + 1) (by omega) rfl
          (fun final => back (replaceLeft final start (f raw[start]! right[start]!)))
      refine ⟨restore, ?_, ?_⟩
      · rw [loop, activeBody start active back]
        simpa only [bind_ok] using eq
      · intro cursor
        rw [applied cursor, apply_step_at raw right f start cursor active]
    · have terminal : start = raw.length := by omega
      subst start
      refine ⟨back, ?_, ?_⟩
      · rw [loop, stopBody back]
        simp only [bind_ok]
      · intro cursor
        rw [mapFrom_full_length]

/-- The original row normalization loop returns the exhausted iterator and
the exact deferred scale writes. The writeback composes with the incoming
backward operation, retaining the supplied later cursor. -/
theorem row_normalization_refines {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (mulLaw : DenseDivRem.MulWordLaw kernels) (inverse : U64) (left right : Slice U64)
    (same : left.length = right.length) (start : Nat) (bound : start ≤ left.length) (back : Back) :
    ∃ restore,
      multiple_loop0_loop1 dictionary kernels (stateAt left right start) back inverse =
        .ok (stateAt left right left.length, restore) ∧
      ∀ cursor, restore (stateAt left right cursor) =
        back (stateAt (mapFrom left right (scaleWord inverse) start) right cursor) := by
  unfold multiple_loop0_loop1
  refine zip_fold _ left right (scaleWord inverse) ?_ ?_ start bound back
  · intro i active restore
    have rightBound : i < right.length := by omega
    simp only [multiple_loop0_loop1.body, next_some_at left right i active rightBound, bind_ok]
    dsimp! only
    rw [Slice.Inhabited_getElem_eq_getElem! right i rightBound, mulLaw]
    simp only [bind_ok, scaleWord]
  · intro restore
    simp only [multiple_loop0_loop1.body,
      next_done_at left right left.length (Or.inl (Nat.le_refl _)), bind_ok]
    rfl

/-- The original witness normalization uses the same checked backward map. -/
theorem witness_normalization_refines {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (mulLaw : DenseDivRem.MulWordLaw kernels) (inverse : U64) (left right : Slice U64)
    (same : left.length = right.length) (start : Nat) (bound : start ≤ left.length) (back : Back) :
    ∃ restore,
      multiple_loop0_loop2 dictionary kernels (stateAt left right start) back inverse =
        .ok (stateAt left right left.length, restore) ∧
      ∀ cursor, restore (stateAt left right cursor) =
        back (stateAt (mapFrom left right (scaleWord inverse) start) right cursor) :=
  row_normalization_refines kernels mulLaw inverse left right same start bound back

end BulksketchBridge.AffineMultiple
