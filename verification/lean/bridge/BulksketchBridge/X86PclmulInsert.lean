import Arithmetic.X86PclmulInsertGenerated
import BulksketchBridge.X86Pclmul
import BulksketchBridge.PortableRebuiltSeed

namespace BulksketchBridge.X86Pclmul

open Aeneas Aeneas.Std Result ControlFlow X86PclmulRuntime
open BulksketchBridge.Algebra.Gf64 BulksketchProofs.Field
open PortableEncoding
open bulksketch.backend.x86_pclmul

set_option maxRecDepth 4096
set_option maxHeartbeats 350000

local notation "portableInner" =>
  bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.insert_nonzero_loop0_loop0
local notation "portableInnerBody" =>
  bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.insert_nonzero_loop0_loop0.body
local notation "portableOuterBody" =>
  bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.insert_nonzero_loop0.body
local notation "portableOuter" =>
  bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.insert_nonzero_loop0
local notation "portableInsert" =>
  bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.insert_nonzero

def registerWord (input : Xmm) : U64 := ⟨low64 input⟩

private theorem low_join_exact (lo hi : BitVec 64) : low64 (join128 lo hi) = lo := by
  apply BitVec.eq_of_getLsbD_eq
  intro i bound
  simp [low64, join128, bound]

private theorem next_register (carryless : Bool) (power square : Xmm) :
    ∃ updated,
      reduced carryless dictionary (clmul128 (low64 power) (low64 square)) = .ok updated ∧
      low updated = .ok (wordMul (registerWord power) (registerWord square)) ∧
      registerWord updated = wordMul (registerWord power) (registerWord square) := by
  let product := clmul128 (low64 power) (low64 square)
  let word := reduceFold64 (low64 product) (high64 product)
  let upper := if carryless then high64 product ^^^ overflow64 (high64 product) else 0
  let updated := join128 word upper
  have normal : reduced carryless dictionary product = .ok updated := by
    simpa only [updated, word, upper, low64, high64] using reduced_refines carryless product
  have scalar : registerWord updated = wordMul (registerWord power) (registerWord square) := by
    unfold registerWord updated
    rw [low_join_exact]
    rfl
  exact ⟨updated, normal, (low_refines updated).trans (congrArg Result.ok scalar), scalar⟩

private theorem next_live (iter : MutIter) (active : iter.i < iter.slice.length) :
    ∃ value next back, core.slice.iter.IteratorIterMut.next iter = .ok (some value, next, back) ∧
      next.i = iter.i + 1 ∧ next.slice = iter.slice := by
  have bound : iter.i < iter.slice.len.val := by simpa using active
  unfold core.slice.iter.IteratorIterMut.next
  rw [dite_eq_left bound]
  exact ⟨_, _, _, rfl, rfl, rfl⟩

private theorem next_exhausted (iter : MutIter) (stopped : iter.slice.length ≤ iter.i) :
    core.slice.iter.IteratorIterMut.next iter = .ok (none, iter, fun later _ => later) := by
  have bound : ¬iter.i < iter.slice.len.val := by simpa using Nat.not_lt.mpr stopped
  unfold core.slice.iter.IteratorIterMut.next
  rw [dite_eq_right bound]

/-- The native register power is represented by its low word. Both
original loops have the same mutable iterator and returned backward
function, including for an already exhausted cursor. -/
theorem insertion_inner_simulates_portable (carryless : Bool) (iter : MutIter) (back : MutIter → MutIter)
    (square power : Xmm) :
    insert_loop0_loop0 carryless dictionary iter back square power =
      portableInner dictionary iter back (registerWord square) (registerWord power) := by
  suffices ∀ remaining (iter : MutIter), iter.slice.length - iter.i = remaining →
      ∀ (back : MutIter → MutIter) (power : Xmm),
        insert_loop0_loop0 carryless dictionary iter back square power =
          portableInner dictionary iter back (registerWord square) (registerWord power) by
    exact this _ iter rfl back power
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
    intro iter measure back power
    by_cases active : iter.i < iter.slice.length
    · obtain ⟨value, next, write, yielded, index, shape⟩ := next_live iter active
      obtain ⟨updated, reducedNormal, lowNormal, exactWord⟩ := next_register carryless power square
      have rawNormal : clmul 0#i32 power square =
          .ok (clmul128 (low64 power) (low64 square)) := rfl
      have portableNormal :
          bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractArithmetic.mul
            dictionary (registerWord power) (registerWord square) =
              .ok (wordMul (registerWord power) (registerWord square)) :=
        (Portable.mul_refines (registerWord power) (registerWord square)).1
      unfold insert_loop0_loop0
        bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.insert_nonzero_loop0_loop0
      conv_lhs => rw [loop]
      conv_rhs => rw [loop]
      dsimp only
      simp only [insert_loop0_loop0.body,
        bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.insert_nonzero_loop0_loop0.body,
        yielded, bind_ok]
      dsimp! only
      rw [rawNormal, bind_ok, reducedNormal, bind_ok, lowNormal, bind_ok, portableNormal, bind_ok]
      simp only [lift, bind_ok]
      let restore := fun later => back (write later (some (value ^^^ wordMul (registerWord power) (registerWord square))))
      have recursive := ih (next.slice.length - next.i) (by rw [shape, index]; omega) next rfl restore updated
      rw [exactWord] at recursive
      simpa only [insert_loop0_loop0, insert_loop0_loop0.body,
        bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.insert_nonzero_loop0_loop0,
        bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.insert_nonzero_loop0_loop0.body,
        lift, bind_ok] using recursive
    · have yielded := next_exhausted iter (by omega)
      unfold insert_loop0_loop0
        bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.insert_nonzero_loop0_loop0
      conv_lhs => rw [loop]
      conv_rhs => rw [loop]
      dsimp only
      simp only [insert_loop0_loop0.body,
        bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.insert_nonzero_loop0_loop0.body,
        yielded, bind_ok]
      dsimp! only
      simp only [bind_ok]

private theorem square_start (id : U64) :
    multiply false dictionary id id = .ok (Square.expectedWord id) := by
  have matched := square_refines id
  change multiply true dictionary id id = .ok (Square.expectedWord id) at matched
  exact (multiply_refines false id id).trans ((multiply_refines true id id).symm.trans matched)

private theorem register_word_roundtrip (word : U64) : registerWord (word.bv.setWidth 128) = word := by
  apply U64.bv_eq_imp_eq
  simp only [registerWord, UScalar.bv_mk_apply, low64]
  simp

private theorem outer_body_simulates_portable (carryless : Bool)
    (iter : core.slice.iter.Iter U64) (first : U64) (successors : Slice U64) :
    insert_loop0.body carryless dictionary iter first successors =
      portableOuterBody dictionary iter first successors := by
  unfold insert_loop0.body bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.insert_nonzero_loop0.body
  rcases iter with ⟨ids, index⟩
  by_cases active : index < ids.length
  · simp only [shared_next ids index active, bind_ok]
    dsimp! only
    simp only [lift, bind_ok]
    rw [square_start, bind_ok, X86Pclmul.word_refines _, bind_ok,
      X86Pclmul.word_refines ids[index]!, bind_ok, (Portable.square_refines ids[index]!).1, bind_ok]
    simp only [bulksketch.MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter,
      Aeneas.Std.core.slice.Slice.iter_mut, bind_ok]
    try dsimp! only
    rw [insertion_inner_simulates_portable, register_word_roundtrip, register_word_roundtrip]
  · simp only [shared_done ids index (by omega), bind_ok]
    rfl

theorem insertion_outer_simulates_portable (carryless : Bool)
    (iter : core.slice.iter.Iter U64) (first : U64) (successors : Slice U64) :
    insert_loop0 carryless dictionary iter first successors =
      portableOuter dictionary iter first successors := by
  unfold insert_loop0 bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.insert_nonzero_loop0
  apply congrArg (fun step => loop step (iter, first, successors))
  funext state
  rcases state with ⟨cursor, head, tail⟩
  exact outer_body_simulates_portable carryless cursor head tail

/-- The exact helper simulates Portable in either reduction mode. -/
def ActualNativePclmulInsertHelper : Prop :=
  ∀ (carryless : Bool) (odd ids : Slice U64),
    bulksketch.backend.x86_pclmul.insert carryless dictionary odd ids =
      portableInsert dictionary odd ids

theorem native_pclmul_insert_helper : ActualNativePclmulInsertHelper := by
  intro carryless odd ids
  simp only [bulksketch.backend.x86_pclmul.insert,
    bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.insert_nonzero,
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter, bind_ok,
    insertion_outer_simulates_portable]
  rfl

/-- The exact original GF64 XMM insertion, including its public trait entry,
has the same complete output as the separately checked original Portable
body. Its low-word invariant preserves every returned iterator write. -/
def ActualNativePclmulInsert : Prop :=
  ∀ odd ids : Slice U64,
    bulksketch.backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractBulkKernels.insert_nonzero
      dictionary odd ids = portableInsert dictionary odd ids

theorem native_pclmul_insert : ActualNativePclmulInsert := by
  intro odd ids
  exact native_pclmul_insert_helper true odd ids

#print axioms native_pclmul_insert_helper
#print axioms native_pclmul_insert

end BulksketchBridge.X86Pclmul
