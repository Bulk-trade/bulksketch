import Arithmetic.X86MaskedMemoryPureGenerated
import BulksketchBridge.X86MaskedMemorySpec
import BulksketchBridge.X86LaneMask
import BulksketchProofs.Field.CLMul
import Mathlib.Data.Fintype.Card

namespace BulksketchBridge.X86MaskedMemory.PureExtraction

open Aeneas Aeneas.Std

private theorem success_before_bind {A B : Type} {computation : Result A}
    {next : A → Result B} {output : B}
    (normal : Aeneas.Std.bind computation next = .ok output) :
    ∃ input, computation = .ok input ∧ next input = .ok output := by
  cases computation using Result.cases with
  | ret input => exact ⟨input, rfl, by simpa only [bind_ok] using normal⟩
  | vis event resume =>
    rw [bind_vis] at normal
    have impossible := congrArg Result.match normal
    simp at impossible
  | div =>
    rw [bind_div] at normal
    have impossible := congrArg Result.match normal
    simp at impossible

/-- In the verbatim pure body, any successful return is the slice obtained
before the store instruction, regardless of the instruction's implementation. -/
theorem store_returns_prewrite_slice {V : Type} (bindings : Bindings V)
    (words : Slice U64) (value : V) (output : Slice U64)
    (normal : backend.x86_vpclmul512.store bindings words value = .ok output) :
    ∃ pointer, bindings.asMutPtr words = .ok (pointer, output) := by
  unfold backend.x86_vpclmul512.store at normal
  obtain ⟨⟨pointer, saved⟩, prewrite, normal⟩ := success_before_bind normal
  dsimp only at normal
  obtain ⟨_, _, normal⟩ := success_before_bind normal
  obtain ⟨_, _, normal⟩ := success_before_bind normal
  obtain ⟨_, _, normal⟩ := success_before_bind normal
  have same : saved = output := Result.ok_injective normal
  exact ⟨pointer, same ▸ prewrite⟩

theorem successful_stores_same_slice {V : Type} (bindings : Bindings V) (words : Slice U64)
    (first second : V) (firstOutput secondOutput : Slice U64)
    (firstRun : backend.x86_vpclmul512.store bindings words first = .ok firstOutput)
    (secondRun : backend.x86_vpclmul512.store bindings words second = .ok secondOutput) :
    firstOutput = secondOutput := by
  obtain ⟨_, firstSlice⟩ := store_returns_prewrite_slice bindings words first firstOutput firstRun
  obtain ⟨_, secondSlice⟩ := store_returns_prewrite_slice bindings words second secondOutput secondRun
  exact congrArg Prod.snd (Result.ok_injective (firstSlice.symm.trans secondSlice))

private def singleton (word : BitVec 64) : Slice U64 := Slice.from [⟨word⟩] (by scalar_tac)

def PureStoreWritebackImpossible : Prop :=
  ∀ bindings : Bindings Lanes,
    ¬ ∀ value : Lanes, backend.x86_vpclmul512.store bindings (singleton 0) value =
      .ok (singleton (value 0))

/-- A one-word destination already rules out a correct pure store with the
generated signatures. Two distinct first lanes demand distinct writeback. -/
theorem pure_store_cannot_writeback : PureStoreWritebackImpossible := by
  intro bindings correct
  have same := successful_stores_same_slice bindings (singleton 0) (fun _ => 0) (fun _ => 1)
    (singleton 0) (singleton 1) (correct _) (correct _)
  have words := congrArg Slice.val same
  have different : (singleton 0).val ≠ (singleton 1).val := by decide
  exact different words

private def twoWords (word : BitVec 128) : Slice U64 :=
  Slice.from [⟨word.setWidth 64⟩, ⟨(word >>> 64).setWidth 64⟩] (by scalar_tac)

private def twoLanes (word : BitVec 128) : Lanes :=
  fun lane => if lane.val = 0 then word.setWidth 64
    else if lane.val = 1 then (word >>> 64).setWidth 64 else 0

private def preparedPointer {V : Type} (bindings : Bindings V) (words : Slice U64) :
    Result (ConstRawPtr I64) := do
  let pointer ← bindings.asPtr words
  bindings.castConst I64 pointer

private theorem load_after_pointer {V : Type} (bindings : Bindings V) (words : Slice U64) :
    backend.x86_vpclmul512.load bindings words = (do
      let mask ← bulksketch.backend.x86_vpclmul512.mask words.len
      let pointer ← preparedPointer bindings words
      bindings.load mask pointer) := by
  simp only [backend.x86_vpclmul512.load, preparedPointer, Aeneas.Std.bind_assoc]

private theorem mask_two_words (word : BitVec 128) :
    bulksketch.backend.x86_vpclmul512.mask (twoWords word).len = .ok 3#u8 := by
  have length : (twoWords word).len = 2#usize := by
    apply UScalar.eq_of_val_eq
    rfl
  rw [length]
  obtain ⟨mask, normal, value, _⟩ := X86LaneMask.mask_refines 2#usize (by simp)
  rw [normal, show mask = 3#u8 from UScalar.eq_of_val_eq (by simpa using value)]

def PureLoadTwoWordsImpossible : Prop :=
  ∀ bindings : Bindings Lanes,
    ¬ ∀ word : BitVec 128, backend.x86_vpclmul512.load bindings (twoWords word) =
      .ok (twoLanes word)

/-- The load signature carries only one 64-bit pointer payload after the
cast. At fixed mask and length, a successful exact two-word load would inject
the entire 128-bit input into that payload. -/
theorem pure_load_cannot_read_two_words : PureLoadTwoWordsImpossible := by
  intro bindings correct
  let encode (input : Fin (2 ^ 128)) : Fin (2 ^ 64) :=
    match (preparedPointer bindings (twoWords ⟨input⟩)).match with
    | .ok pointer => pointer.v.bv.toFin
    | _ => 0
  have factor (word : BitVec 128) : ∃ pointer,
      preparedPointer bindings (twoWords word) = .ok pointer ∧
      bindings.load 3#u8 pointer = .ok (twoLanes word) := by
    have normal := correct word
    rw [load_after_pointer, mask_two_words, bind_ok] at normal
    exact success_before_bind normal
  have injective : Function.Injective encode := by
    intro x y same
    obtain ⟨p, pNormal, xRead⟩ := factor ⟨x⟩
    obtain ⟨q, qNormal, yRead⟩ := factor ⟨y⟩
    simp only [encode, pNormal, qNormal, Result.match.ok] at same
    have scalar : p.v = q.v := I64.bv_eq_imp_eq _ _
      (congrArg (fun input : Fin (2 ^ 64) => (⟨input⟩ : BitVec 64)) same)
    have pointer : p = q := congrArg (fun value : I64 => (⟨value⟩ : ConstRawPtr I64)) scalar
    have lanes := Result.ok_injective (xRead.symm.trans (pointer ▸ yRead))
    have low := congrArg (fun values : Lanes => values 0) lanes
    have high := congrArg (fun values : Lanes => values 1) lanes
    change (⟨x⟩ : BitVec 128).setWidth 64 = (⟨y⟩ : BitVec 128).setWidth 64 at low
    change ((⟨x⟩ : BitVec 128) >>> 64).setWidth 64 = ((⟨y⟩ : BitVec 128) >>> 64).setWidth 64 at high
    have packed : (⟨x⟩ : BitVec 128) = ⟨y⟩ := by
      have joined := congrArg₂ BulksketchProofs.Field.join128 low high
      simpa only [BulksketchProofs.Field.join128_split] using joined
    exact congrArg BitVec.toFin packed
  have count := Fintype.card_le_of_injective encode injective
  simp only [Fintype.card_fin] at count
  exact (by decide : ¬ (2 ^ 128 : Nat) ≤ 2 ^ 64) count

end BulksketchBridge.X86MaskedMemory.PureExtraction
