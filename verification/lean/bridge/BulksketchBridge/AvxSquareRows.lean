import BulksketchBridge.AvxSquareSeed
import BulksketchBridge.Avx512Register
import BulksketchBridge.X86MaskedMemoryRegister
import BulksketchBridge.ClosedLeafWindows

namespace BulksketchBridge.AvxSquare

open Aeneas Aeneas.Std Aeneas.Std.Avx512Register Aeneas.Std.AvxSquareRuntime
open BulksketchBridge.Avx512RegisterChallenges
open bulksketch.backend.x86_vpclmul512
open scoped BulksketchBridge.DenseMulReductionSpec

set_option maxRecDepth 4096
set_option maxHeartbeats 1400000

def loadWords (words : Slice U64) : Word512 :=
  fun pair half =>
    let index := (X86MaskedMemory.flatIndex pair half).val
    if index < words.length then words[index]!.bv else 0

def storeWords (words : Slice U64) (register : Word512) (bound : words.length ≤ 8) : Slice U64 :=
  Slice.from ((X86MaskedMemory.registerPayload register words.length bound).map (fun bits => (⟨bits⟩ : U64))) (by
    simpa [X86MaskedMemory.registerPayload] using words.length_ineq)

def LoadLaw (read : Load) : Prop :=
  ∀ words : Slice U64, words.length ≤ 8 → read words = .ok (loadWords words)

def StoreLaw (write : Store) : Prop :=
  ∀ (words : Slice U64) (register : Word512) (bound : words.length ≤ 8),
    write words register = .ok (storeWords words register bound)

abbrev enumerateInst (T : Type) :=
  core.iter.traits.iterator.IteratorEnumerate (core.iter.traits.iterator.IteratorSliceIter T)

def skipAt {T : Type} (input : Slice T) (index count : Usize) : Skip (Enumerate T) :=
  ⟨enumerateAt input index, count⟩

private theorem drop_normal {T : Type} [Inhabited T] (input : Slice T) (index : Usize)
    (bound : index.val ≤ input.length) (count : Nat) :
    ∃ next : Usize, next.val = min (index.val + count) input.length ∧
      core.iter.adapters.step_by.skipN (enumerateInst T) (enumerateAt input index) count =
        .ok (enumerateAt input next) := by
  induction count generalizing index with
  | zero => exact ⟨index, by simp [Nat.min_eq_left bound], rfl⟩
  | succ count ih =>
    by_cases active : index.val < input.length
    · obtain ⟨next, value, normal⟩ := enumerate_active input index active
      obtain ⟨last, lastValue, dropped⟩ := ih next (by omega)
      refine ⟨last, by rw [lastValue, value]; congr 1; omega, ?_⟩
      simp only [core.iter.adapters.step_by.skipN, enumerateInst,
        core.iter.traits.iterator.IteratorEnumerate, normal, bind_ok]
      exact dropped
    · refine ⟨index, by rw [Nat.min_eq_right (by omega)]; omega, ?_⟩
      simp only [core.iter.adapters.step_by.skipN, enumerateInst,
        core.iter.traits.iterator.IteratorEnumerate, enumerate_done input index (by omega), bind_ok]
      rfl

theorem skip_active {T : Type} [Inhabited T] (input : Slice T) (index count : Usize)
    (active : index.val + count.val < input.length) :
    ∃ atIndex next : Usize, atIndex.val = index.val + count.val ∧ next.val = atIndex.val + 1 ∧
      skipNext (enumerateInst T) (skipAt input index count) =
        .ok (some (atIndex, input[atIndex.val]!), skipAt input next 0#usize) := by
  obtain ⟨atIndex, value, dropped⟩ := drop_normal input index (by omega) count.val
  rw [Nat.min_eq_left (by omega)] at value
  obtain ⟨next, nextValue, normal⟩ := enumerate_active input atIndex (by omega)
  refine ⟨atIndex, next, value, nextValue, ?_⟩
  simp only [skipNext, skipAt, dropped, bind_ok, enumerateInst,
    core.iter.traits.iterator.IteratorEnumerate, normal]
  rfl

theorem skip_done {T : Type} [Inhabited T] (input : Slice T) (index count : Usize)
    (indexBound : index.val ≤ input.length) (done : input.length ≤ index.val + count.val) :
    ∃ terminal : Skip (Enumerate T),
      skipNext (enumerateInst T) (skipAt input index count) = .ok (none, terminal) := by
  obtain ⟨last, value, dropped⟩ := drop_normal input index indexBound count.val
  rw [Nat.min_eq_right done] at value
  refine ⟨skipAt input last 0#usize, ?_⟩
  simp only [skipNext, skipAt, dropped, bind_ok, enumerateInst,
    core.iter.traits.iterator.IteratorEnumerate, enumerate_done input last (by omega)]
  rfl

def xorRegister (left right : Word512) : Word512 :=
  fun pair half => left pair half ^^^ right pair half

def rowRegion (table : Slice U64) (degree firstHigh index offset stop : Nat) : Slice U64 :=
  let start := (index - firstHigh) * degree
  ClosedLeaf.region table (start + offset) (start + stop)

def rowStep (square : U64) (table : Slice U64) (degree firstHigh index offset stop : Nat)
    (even odd : Word512) : Word512 × Word512 :=
  let lanes := loadWords (rowRegion table degree firstHigh index offset stop)
  let scale : Word512 := fun _ _ => square.bv
  (xorRegister even (products scale lanes false), xorRegister odd (products scale lanes true))

def scanRows (scratch : Slice Raw) (table : Slice U64)
    (degree firstHigh index offset stop : Nat) (even odd : Word512) : Nat → Word512 × Word512
  | 0 => (even, odd)
  | count + 1 =>
    let updated := rowStep scratch[index]!.lo table degree firstHigh index offset stop even odd
    scanRows scratch table degree firstHigh (index + 1) offset stop updated.1 updated.2 count

private theorem signedBits (word : U64) :
    (core.num.I64.from_le_bytes (core.num.U64.to_le_bytes word)).bv = word.bv := by
  have packed := X86Pclmul.word_refines word
  simp only [bulksketch.backend.x86_pclmul.word, X86PclmulRuntime.unsignedBytes,
    X86PclmulRuntime.signedFromBytes, X86PclmulRuntime.moveIn, bind_ok] at packed
  have equality := Result.ok_injective packed
  have narrowed := congrArg (fun bits : BitVec 128 => bits.setWidth 64) equality
  simpa only [BitVec.setWidth_setWidth_of_le _ (by decide : 64 ≤ 128), BitVec.setWidth_eq] using narrowed

/-- Original high-row iteration, with exact masked row read and the two
unreduced even and odd register writebacks. -/
theorem high_row_active (loadModel : Load) (loadLaw : LoadLaw loadModel)
    (scratch : Slice Raw) (table : Slice U64) (degree firstHigh offset stop index skipCount : Usize)
    (even odd : Word512) (active : index.val + skipCount.val < scratch.length)
    (startHigh : firstHigh.val ≤ index.val + skipCount.val)
    (firstHighVal : firstHigh.val = (degree.val + 1) / 2)
    (aBound : scratch.length ≤ degree.val)
    (window : offset.val ≤ stop.val ∧ stop.val ≤ degree.val ∧ stop.val - offset.val ≤ 8)
    (tableBound : degree.val / 2 * degree.val ≤ table.length) :
    ∃ atIndex next : Usize, atIndex.val = index.val + skipCount.val ∧ next.val = atIndex.val + 1 ∧
      square_mod_loop1_loop0.body loadModel table degree firstHigh offset stop
        (skipAt scratch index skipCount) even odd =
      .ok (.cont (skipAt scratch next 0#usize,
        rowStep scratch[atIndex.val]!.lo table degree.val firstHigh.val atIndex.val offset.val stop.val even odd)) := by
  obtain ⟨atIndex, next, atVal, nextVal, iteration⟩ := skip_active scratch index skipCount active
  have tableMax : table.length ≤ Usize.max := table.length_ineq
  have rowBound : atIndex.val - firstHigh.val + 1 ≤ degree.val / 2 := by omega
  have boundRows : (atIndex.val - firstHigh.val + 1) * degree.val ≤ table.length :=
    (Nat.mul_le_mul_right degree.val rowBound).trans tableBound
  rw [Nat.add_mul, Nat.one_mul] at boundRows
  obtain ⟨row, sub, rowVal, _⟩ := RawMulTable.normal_of_spec _ _
    (Usize.sub_spec (x := atIndex) (y := firstHigh) (by omega))
  change row.val = atIndex.val - firstHigh.val at rowVal
  obtain ⟨start, mul, startVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.mul_spec (x := row) (y := degree) (by rw [rowVal]; omega))
  change start.val = row.val * degree.val at startVal
  rw [rowVal] at startVal
  obtain ⟨low, addedLow, lowVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := start) (y := offset) (by rw [startVal]; omega))
  obtain ⟨high, addedHigh, highVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := start) (y := stop) (by rw [startVal]; omega))
  have rangeNormal := ClosedLeaf.shared_region_normal table low high (by omega) (by omega)
  have length := ClosedLeaf.region_length table low.val high.val (by omega)
  have fits : (ClosedLeaf.region table low.val high.val).length ≤ 8 := by omega
  have loaded := loadLaw (ClosedLeaf.region table low.val high.val) fits
  rw [lowVal, highVal, startVal] at loaded
  refine ⟨atIndex, next, atVal, nextVal, ?_⟩
  simp only [square_mod_loop1_loop0.body, iteration, bind_ok]
  dsimp! only
  simp only [sub, mul, addedLow, addedHigh, bind_ok, X86PclmulRuntime.unsignedBytes,
    X86PclmulRuntime.signedFromBytes, broadcast, signedBits, Slice.index_SliceIndexRangeUsizeSliceInst,
    rangeNormal, loaded, xorWords, rowStep, rowRegion, lowVal, highVal,
    startVal, xorRegister]
  rw [Avx512Register.raw_refines _ _]
  simp only [bind_ok]
  rfl

/-- Exact high-row scan, including the initially skipped prefix and empty
high input. The scalar specification retains unreduced even and odd halves. -/
theorem high_loop_refines (loadModel : Load) (loadLaw : LoadLaw loadModel)
    (scratch : Slice Raw) (table : Slice U64) (degree firstHigh offset stop index skipCount : Usize)
    (even odd : Word512) (cursor : index.val ≤ scratch.length)
    (startHigh : firstHigh.val ≤ index.val + skipCount.val)
    (firstHighVal : firstHigh.val = (degree.val + 1) / 2)
    (aBound : scratch.length ≤ degree.val)
    (window : offset.val ≤ stop.val ∧ stop.val ≤ degree.val ∧ stop.val - offset.val ≤ 8)
    (tableBound : degree.val / 2 * degree.val ≤ table.length) :
    square_mod_loop1_loop0 loadModel (skipAt scratch index skipCount) table degree firstHigh offset stop even odd =
      .ok (scanRows scratch table degree.val firstHigh.val (index.val + skipCount.val)
        offset.val stop.val even odd (scratch.length - (index.val + skipCount.val))) := by
  suffices loopCase : ∀ remaining (i skip : Usize) (even odd : Word512),
      i.val ≤ scratch.length → firstHigh.val ≤ i.val + skip.val →
      scratch.length - (i.val + skip.val) = remaining →
      square_mod_loop1_loop0 loadModel (skipAt scratch i skip) table degree firstHigh offset stop even odd =
        .ok (scanRows scratch table degree.val firstHigh.val (i.val + skip.val)
          offset.val stop.val even odd remaining) from
    loopCase _ index skipCount even odd cursor startHigh rfl
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
    intro i skip even odd bounded first remainingEq
    by_cases active : i.val + skip.val < scratch.length
    · obtain ⟨atIndex, next, atVal, nextVal, body⟩ :=
        high_row_active loadModel loadLaw scratch table degree firstHigh offset stop i skip even odd
          active first firstHighVal aBound window tableBound
      have decrease : scratch.length - (next.val + (0#usize).val) < remaining := by
        simp only [show (0#usize).val = 0 by simp, Nat.add_zero]; omega
      have countEq : remaining = scratch.length - (next.val + (0#usize).val) + 1 := by
        simp only [show (0#usize).val = 0 by simp, Nat.add_zero]; omega
      let updated := rowStep scratch[atIndex.val]!.lo table degree.val firstHigh.val atIndex.val offset.val stop.val even odd
      rw [countEq, scanRows, ← atVal, ← nextVal]
      conv => lhs; unfold square_mod_loop1_loop0 loop
      dsimp only
      rw [body]
      simp only [bind_ok]
      change square_mod_loop1_loop0 loadModel (skipAt scratch next 0#usize) table degree firstHigh offset stop
        updated.1 updated.2 = _
      simpa only [show (0#usize).val = 0 by simp, Nat.add_zero] using
        (ih _ decrease next 0#usize updated.1 updated.2 (by omega) (by omega) rfl)
    · have stopped : scratch.length ≤ i.val + skip.val := by omega
      have finished : remaining = 0 := by omega
      rw [finished, scanRows]
      obtain ⟨terminal, exhausted⟩ := skip_done scratch i skip bounded stopped
      have body : square_mod_loop1_loop0.body loadModel table degree firstHigh offset stop
          (skipAt scratch i skip) even odd = .ok (.done (even, odd)) := by
        simp only [square_mod_loop1_loop0.body, exhausted, bind_ok]
        rfl
      conv => lhs; unfold square_mod_loop1_loop0 loop
      dsimp only
      rw [body, bind_ok]

end BulksketchBridge.AvxSquare
