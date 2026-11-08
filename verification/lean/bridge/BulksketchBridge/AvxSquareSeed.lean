import Arithmetic.AvxSquareGenerated
import BulksketchBridge.X86Pclmul
import BulksketchBridge.RebuiltLocatorLoop
import BulksketchBridge.DenseMulReductionSpec
import BulksketchBridge.ClosedLeafAdvance
import BulksketchBridge.ReconstructionLoop

namespace BulksketchBridge.AvxSquare

open Aeneas Aeneas.Std
open scoped BulksketchBridge.DenseMulReductionSpec
open bulksketch.backend.x86_vpclmul512

set_option maxRecDepth 4096

abbrev Raw := bulksketch.types.RawProduct
abbrev Enumerate (T : Type) := core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter T)

def enumerateAt {T : Type} (a : Slice T) (count : Usize) : Enumerate T :=
  ⟨⟨a, count.val⟩, count⟩

theorem enumerate_active {T : Type} [Inhabited T] (a : Slice T) (count : Usize)
    (active : count.val < a.length) :
    ∃ next : Usize, next.val = count.val + 1 ∧
      core.iter.adapters.enumerate.IteratorEnumerate.next
        (core.iter.traits.iterator.IteratorSliceIter T) (enumerateAt a count) =
        .ok (some (count, a[count.val]!), enumerateAt a next) := by
  have safe : count.val + (1#usize).val ≤ Usize.max := by
    have capacity : a.length ≤ Usize.max := a.length_ineq
    simp only [show (1#usize).val = 1 by simp]
    omega
  obtain ⟨next, normal, value⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := count) (y := 1#usize) safe)
  have nextValue : next.val = count.val + 1 := by simpa using value
  have active' : count.val < (Slice.len a).val := by rwa [Slice.len_val]
  have inner : core.slice.iter.IteratorSliceIter.next ⟨a, count.val⟩ =
      .ok (some a[count.val]!, ⟨a, count.val + 1⟩) := by
    simp only [core.slice.iter.IteratorSliceIter.next, active', _root_.dite_true]
    exact congrArg (fun item => Result.ok (some item, (⟨a, count.val + 1⟩ : core.slice.iter.Iter T)))
      (Slice.Inhabited_getElem_eq_getElem! a count.val active)
  refine ⟨next, nextValue, ?_⟩
  simp only [core.iter.adapters.enumerate.IteratorEnumerate.next, enumerateAt, inner,
    bind_ok, normal, nextValue]
  rfl

theorem enumerate_done {T : Type} (a : Slice T) (count : Usize) (done : a.length ≤ count.val) :
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter T) (enumerateAt a count) =
      .ok (none, enumerateAt a count) := by
  have inactive : ¬ count.val < (Slice.len a).val := by rw [Slice.len_val]; omega
  have inner : core.slice.iter.IteratorSliceIter.next ⟨a, count.val⟩ =
      .ok (none, ⟨a, count.val⟩) := by
    simp only [core.slice.iter.IteratorSliceIter.next, inactive, _root_.dite_false]
  simp only [core.iter.adapters.enumerate.IteratorEnumerate.next, enumerateAt, inner, bind_ok]
  rfl

def seedStep (coefficient : U64) (index firstHigh : Nat)
    (dst : Slice U64) (scratch : Slice Raw) : Slice U64 × Slice Raw :=
  let square := Square.expectedWord coefficient
  (if index < firstHigh then dst.setAtNat (2 * index) square else dst,
    scratch.setAtNat index { scratch[index]! with lo := square })

def seed (input : Slice U64) (index firstHigh : Nat)
    (dst : Slice U64) (scratch : Slice Raw) : Nat → Slice U64 × Slice Raw
  | 0 => (dst, scratch)
  | count + 1 =>
    let updated := seedStep input[index]! index firstHigh dst scratch
    seed input (index + 1) firstHigh updated.1 updated.2 count

@[simp] theorem seed_step_dst_length (word : U64) (index firstHigh : Nat)
    (dst : Slice U64) (scratch : Slice Raw) :
    (seedStep word index firstHigh dst scratch).1.length = dst.length := by
  unfold seedStep
  split <;> simp only [Slice.setAtNat_length]

@[simp] theorem seed_step_scratch_length (word : U64) (index firstHigh : Nat)
    (dst : Slice U64) (scratch : Slice Raw) :
    (seedStep word index firstHigh dst scratch).2.length = scratch.length :=
  Slice.setAtNat_length ..

theorem seed_body_active (input dst : Slice U64) (scratch : Slice Raw)
    (index firstHigh : Usize)
    (active : index.val < input.length) (scratchRoom : input.length ≤ scratch.length)
    (firstHighVal : firstHigh.val = (dst.length + 1) / 2) :
    ∃ next : Usize, next.val = index.val + 1 ∧
      square_mod_loop0.body firstHigh (enumerateAt input index) dst scratch =
        .ok (.cont (enumerateAt input next, seedStep input[index.val]! index.val firstHigh.val dst scratch)) := by
  obtain ⟨next, nextValue, enumeration⟩ := enumerate_active input index active
  have square := X86Pclmul.square_refines input[index.val]!
  refine ⟨next, nextValue, ?_⟩
  have readBound : index.val < scratch.length := by omega
  obtain ⟨value, read, readVal⟩ := RawMulTable.normal_of_spec _ _
    (Slice.index_usize_spec scratch index readBound)
  have old : value = scratch[index.val]! := by
    rw [← Slice.Inhabited_getElem_eq_getElem! scratch index.val readBound]
    exact readVal
  simp only [square_mod_loop0.body, enumeration, bind_ok]
  dsimp! only
  simp only [square, bind_ok, Slice.index_mut_usize, read, old, UScalar.lt_equiv, Bind.bind]
  dsimp! only
  by_cases low : index.val < firstHigh.val
  · have indexBound : 2 * index.val < dst.length := by omega
    have dstMax : dst.length ≤ Usize.max := dst.length_ineq
    obtain ⟨twice, mul, mulVal⟩ := RawMulTable.normal_of_spec _ _
      (Usize.mul_spec (x := 2#usize) (y := index) (by change 2 * index.val ≤ Usize.max; omega))
    change twice.val = 2 * index.val at mulVal
    have write := Reconstruction.update_normal dst twice (Square.expectedWord input[index.val]!) (by omega)
    simp only [low, ite_true, mul, bind_ok, write, seedStep, Slice.set, mulVal]
  · simp only [low, ite_false, seedStep, Slice.set]

/-- Exact source first pass. Each input is squared once, the raw low slot
is written, and only low coefficients seed their even destination slot. -/
theorem seed_loop_refines (input dst : Slice U64) (scratch : Slice Raw) (index firstHigh : Usize)
    (scratchRoom : input.length ≤ scratch.length)
    (firstHighVal : firstHigh.val = (dst.length + 1) / 2) (cursor : index.val ≤ input.length) :
    square_mod_loop0 (enumerateAt input index) dst scratch firstHigh =
      .ok (seed input index.val firstHigh.val dst scratch (input.length - index.val)) := by
  suffices loopCase : ∀ remaining (i : Usize) (out : Slice U64) (raw : Slice Raw),
      i.val ≤ input.length → input.length - i.val = remaining →
      input.length ≤ raw.length → firstHigh.val = (out.length + 1) / 2 →
      square_mod_loop0 (enumerateAt input i) out raw firstHigh =
        .ok (seed input i.val firstHigh.val out raw remaining) from
    loopCase _ index dst scratch cursor rfl scratchRoom firstHighVal
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
    intro i out raw bounded remainingEq room highVal
    by_cases active : i.val < input.length
    · obtain ⟨next, nextValue, body⟩ := seed_body_active input out raw i firstHigh active room highVal
      have decrease : input.length - next.val < remaining := by omega
      have countEq : remaining = input.length - next.val + 1 := by omega
      rw [countEq, seed, ← nextValue]
      conv => lhs; unfold square_mod_loop0 loop
      dsimp only
      rw [body]
      simp only [bind_ok]
      exact ih _ decrease next (seedStep input[i.val]! i.val firstHigh.val out raw).1
        (seedStep input[i.val]! i.val firstHigh.val out raw).2 (by omega) rfl (by simpa) (by simpa)
    · have stopped : input.length ≤ i.val := by omega
      have finished : remaining = 0 := by omega
      rw [finished, seed]
      have body : square_mod_loop0.body firstHigh (enumerateAt input i) out raw = .ok (.done (out, raw)) := by
        simp only [square_mod_loop0.body, enumerate_done input i stopped, bind_ok]
        rfl
      conv => lhs; unfold square_mod_loop0 loop
      dsimp only
      rw [body, bind_ok]

end BulksketchBridge.AvxSquare
