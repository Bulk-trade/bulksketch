import Arithmetic.AffineSubspacesGenerated
import BulksketchBridge.RawMulTable

namespace BulksketchBridge.RootRun

open Aeneas Aeneas.Std

def subspaceStart (rank : Nat) : Nat := rank * (rank + 1) / 2

def ActualSubspaceStart : Prop :=
  ∀ rank : Usize, rank.val ≤ 64 →
    ∃ offset : Usize, bulksketch.decode.affine.subspace_start rank = .ok offset ∧
      offset.val = subspaceStart rank.val

private theorem small_usize : 4160 ≤ Usize.max := by
  simp only [Usize.max, Usize.numBits, UScalarTy.numBits]
  rcases System.Platform.numBits_eq with width | width <;> rw [width] <;> decide

theorem subspace_start_refines : ActualSubspaceStart := by
  intro rank rankBound
  have product : rank.val * (rank.val + 1) ≤ Usize.max := by
    exact (Nat.mul_le_mul rankBound (by omega : rank.val + 1 ≤ 65)).trans small_usize
  obtain ⟨next, addOk, nextVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := rank) (y := 1#usize) (by have := small_usize; change rank.val + 1 ≤ Usize.max; omega))
  change next.val = rank.val + 1 at nextVal
  obtain ⟨mul, mulOk, mulVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.mul_spec (x := rank) (y := next) (by rw [nextVal]; exact product))
  obtain ⟨offset, divOk, divVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.div_spec mul (y := 2#usize) (by simp))
  refine ⟨offset, ?_, ?_⟩
  · simp only [bulksketch.decode.affine.subspace_start, addOk, mulOk, divOk, bind_ok]
  · change offset.val = mul.val / 2 at divVal
    rw [divVal, mulVal, nextVal]
    rfl

end BulksketchBridge.RootRun
