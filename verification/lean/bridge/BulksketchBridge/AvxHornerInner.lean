import Arithmetic.AvxHornerGenerated
import BulksketchBridge.HornerPolynomial
import BulksketchBridge.AvxSquareWindows

namespace BulksketchBridge.AvxHorner

open Aeneas Aeneas.Std Aeneas.Std.Avx512Register
open BulksketchBridge.Avx512RegisterChallenges AvxSquare PortableHornerChallenges
open bulksketch.backend.x86_vpclmul512

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

def splat (word : U64) : Word512 := fun _ _ => word.bv

def registerStep (points value : Word512) (coefficient : U64) : Word512 :=
  xorRegister (productsReduced value points) (splat coefficient)

private theorem signed_bits (word : U64) :
    (core.num.I64.from_le_bytes (core.num.U64.to_le_bytes word)).bv = word.bv := by
  have packed := X86Pclmul.word_refines word
  simp only [bulksketch.backend.x86_pclmul.word, X86PclmulRuntime.unsignedBytes,
    X86PclmulRuntime.signedFromBytes, X86PclmulRuntime.moveIn, bind_ok] at packed
  have equality := Result.ok_injective packed
  have narrowed := congrArg (fun bits : BitVec 128 => bits.setWidth 64) equality
  simpa only [BitVec.setWidth_setWidth_of_le _ (by decide : 64 ≤ 128), BitVec.setWidth_eq] using narrowed

theorem broadcast_normal (word : U64) :
    (do
      let bytes ← X86PclmulRuntime.unsignedBytes word
      let signed ← X86PclmulRuntime.signedFromBytes bytes
      broadcast signed) = Result.ok (splat word) := by
  simp only [X86PclmulRuntime.unsignedBytes, X86PclmulRuntime.signedFromBytes,
    broadcast, bind_ok, signed_bits]
  rfl

private abbrev doubleEnded :=
  bulksketch.core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT U64

abbrev Reverse := core.iter.adapters.rev.Rev (core.slice.iter.Iter U64)

def reverseAt (rest : Slice U64) : Reverse := ⟨⟨rest, 0⟩⟩

private theorem rev_next {iterator next : core.slice.iter.Iter U64} {item : Option U64}
    (step : core.slice.iter.IteratorSliceIter.next_back iterator = Result.ok (item, next)) :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next doubleEnded ⟨iterator⟩ =
      Result.ok (item, ⟨next⟩) := by
  change (do
    let (item, next) ← core.slice.iter.IteratorSliceIter.next_back iterator
    Result.ok (item, (⟨next⟩ : Reverse))) = _
  rw [step]
  exact bind_ok (item, next) _

/-- The complete original inner register loop is the reverse coefficient fold
for both of the register reduction modes. -/
theorem inner_loop (cl : Bool) (points value : Word512) (rest : Slice U64) :
    horner_kernel_loop0_loop0 cl (reverseAt rest) points value =
      Result.ok (rest.val.reverse.foldl (registerStep points) value) := by
  suffices ∀ remaining (rest : Slice U64) (value : Word512), rest.val.reverse = remaining →
      horner_kernel_loop0_loop0 cl (reverseAt rest) points value =
        Result.ok (remaining.foldl (registerStep points) value) from this rest.val.reverse rest value rfl
  intro remaining
  induction remaining with
  | nil =>
    intro rest value reversed
    have empty : rest.val = [] := List.reverse_eq_nil_iff.mp reversed
    have next : core.slice.iter.IteratorSliceIter.next_back ⟨rest, 0⟩ =
        Result.ok (none, ⟨rest, 0⟩) := by
      unfold core.slice.iter.IteratorSliceIter.next_back
      split
      · rename_i active
        change 0 < rest.val.length at active
        simp [empty] at active
      · rfl
    have bodyDone : horner_kernel_loop0_loop0.body cl points (reverseAt rest) value =
        Result.ok (ControlFlow.done value) := by
      simp only [horner_kernel_loop0_loop0.body, reverseAt, rev_next next, bind_ok]
      rfl
    unfold horner_kernel_loop0_loop0 loop
    dsimp only
    rw [bodyDone, bind_ok]
    rfl
  | cons coefficient remaining ih =>
    intro rest value reversed
    have positive : 0 < rest.val.length := by
      have nonempty : rest.val ≠ [] := by intro empty; simp [empty] at reversed
      exact List.length_pos_iff.mpr nonempty
    obtain ⟨⟨item, next⟩, normal, itemEq, nextVals, nextCursor⟩ :=
      RawMulTable.normal_of_spec _ _ (core.slice.iter.IteratorSliceIter.next_back.spec
        (⟨rest, 0⟩ : core.slice.iter.Iter U64) positive)
    have itemExact : item = some coefficient := by
      change item = rest.val.getLast? at itemEq
      rw [itemEq, List.getLast?_eq_head?_reverse]
      simp [reversed]
    have nextExact : next = ⟨next.slice, 0⟩ := by cases next; simp_all
    have nextReversed : next.slice.val.reverse = remaining := by
      change next.slice.val = rest.val.take (rest.val.length - 1) at nextVals
      rw [nextVals, ← List.dropLast_eq_take]
      have original : rest.val = remaining.reverse ++ [coefficient] := by
        simpa using congrArg List.reverse reversed
      simp [original]
    have nextStep : core.slice.iter.IteratorSliceIter.next_back ⟨rest, 0⟩ =
        Result.ok (some coefficient, ⟨next.slice, 0⟩) := by
      rw [normal, itemExact, nextExact]
    have bodyStep : horner_kernel_loop0_loop0.body cl points (reverseAt rest) value =
        Result.ok (ControlFlow.cont (reverseAt next.slice, registerStep points value coefficient)) := by
      simp only [horner_kernel_loop0_loop0.body, reverseAt, rev_next nextStep, bind_ok]
      dsimp! only
      have mul := Avx512Register.multiply_refines cl value points
      simp only [mul, X86PclmulRuntime.unsignedBytes, X86PclmulRuntime.signedFromBytes,
        broadcast, signed_bits, xorWords, bind_ok, registerStep]
      rfl
    conv_lhs => unfold horner_kernel_loop0_loop0 loop
    dsimp only
    rw [bodyStep, bind_ok]
    exact ih next.slice (registerStep points value coefficient) nextReversed

theorem lane_fold (remaining : List U64) (points value : Word512) (pair : Fin 4) (high : Bool) :
    (remaining.foldl (registerStep points) value) pair high =
      (remaining.foldl (stepWord ⟨points pair high⟩) ⟨value pair high⟩).bv := by
  induction remaining generalizing value with
  | nil => rfl
  | cons coefficient remaining ih =>
    rw [List.foldl_cons, List.foldl_cons, ih]
    rfl

end BulksketchBridge.AvxHorner
