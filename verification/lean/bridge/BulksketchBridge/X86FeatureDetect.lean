import Arithmetic.X86FeatureDetectGenerated
import Mathlib.Tactic.IntervalCases

namespace BulksketchBridge.X86FeatureDetect

open Aeneas Aeneas.Std X86FeatureDetectRuntime

def cpuAvailable (snapshot : Snapshot) : Bool :=
  snapshot.leaf7.ebx.bv.getLsbD 16 && snapshot.leaf7.ecx.bv.getLsbD 10

def xsaveAvailable (snapshot : Snapshot) : Bool :=
  snapshot.leaf1.ecx.bv.getLsbD 26 && snapshot.leaf1.ecx.bv.getLsbD 27

def xcr0Available (snapshot : Snapshot) : Bool :=
  snapshot.xcr0.bv.getLsbD 1 && snapshot.xcr0.bv.getLsbD 2 &&
    snapshot.xcr0.bv.getLsbD 5 && snapshot.xcr0.bv.getLsbD 6 && snapshot.xcr0.bv.getLsbD 7

/-- The original detector returns normally on all register snapshots under
the scoped read model. In particular, XGETBV is unavailable when the
XSAVE guard is false. -/
def DetectRefines : Prop :=
  ∀ snapshot : Snapshot, bulksketch.backend.x86_vpclmul512.detect snapshot =
    Result.ok (cpuAvailable snapshot && (xsaveAvailable snapshot && xcr0Available snapshot))

def SupportedRefines : Prop :=
  ∀ cpu os : Bool, bulksketch.backend.detect.vpclmul512_supported cpu os =
    Result.ok (cpu && os)

theorem supported_refines : SupportedRefines := by
  intro cpu os
  cases cpu <;> rfl

private theorem masked_eq {width : Nat} (word mask : BitVec width) :
    word &&& mask = mask ↔
      ∀ i, i < width → mask.getLsbD i = true → word.getLsbD i = true := by
  constructor
  · intro equal i _ enabled
    have atBit := congrArg (fun bits : BitVec width => bits.getLsbD i) equal
    simpa only [BitVec.getLsbD_and, enabled, Bool.and_true] using atBit
  · intro check
    apply BitVec.eq_of_getLsbD_eq
    intro i inside
    rw [BitVec.getLsbD_and]
    cases bit : mask.getLsbD i with
    | false => simp [bit]
    | true => simp [bit, check i inside bit]

private theorem masked_zero {width : Nat} (word mask : BitVec width) :
    word &&& mask = 0 ↔
      ∀ i, i < width → mask.getLsbD i = true → word.getLsbD i = false := by
  constructor
  · intro equal i _ enabled
    have atBit := congrArg (fun bits : BitVec width => bits.getLsbD i) equal
    simpa [BitVec.getLsbD_and, enabled] using atBit
  · intro check
    apply BitVec.eq_of_getLsbD_eq
    intro i inside
    rw [BitVec.getLsbD_and]
    cases bit : mask.getLsbD i with
    | false => simp [bit]
    | true => simp [bit, check i inside bit]

private theorem word_test (word mask : U32) (index : Nat) (bounded : index < 32)
    (selects : ∀ i, i < 32 → mask.bv.getLsbD i = decide (i = index)) :
    ((word &&& mask) != 0#u32) = word.bv.getLsbD index := by
  have zero : (word &&& mask) = 0#u32 ↔ word.bv.getLsbD index = false := by
    constructor
    · intro eq
      have exactBits : word.bv &&& mask.bv = 0 := congrArg U32.bv eq
      exact (masked_zero _ _).mp exactBits index bounded (by simp [selects index bounded])
    · intro unset
      apply U32.bv_eq_imp_eq
      apply (masked_zero _ _).mpr
      intro i inside active
      have same : i = index := by simpa only [selects i inside, decide_eq_true_eq] using active
      simpa only [same] using unset
  cases selected : word.bv.getLsbD index with
  | false => simp [zero.mpr selected]
  | true =>
    have nonzero : (word &&& mask) ≠ 0#u32 := by
      intro eq
      have opposite := zero.mp eq
      simp [selected] at opposite
    simp [nonzero]

private theorem xsave_test (snapshot : Snapshot) :
    (snapshot.leaf1.ecx &&& 201326592#u32 = 201326592#u32) ↔ xsaveAvailable snapshot = true := by
  let word := snapshot.leaf1.ecx
  have selects (i : Nat) (bounded : i < 32) :
      (201326592#u32).bv.getLsbD i = decide (i = 26 ∨ i = 27) := by
    interval_cases i <;> decide +kernel
  change (word &&& 201326592#u32 = 201326592#u32) ↔
    (word.bv.getLsbD 26 && word.bv.getLsbD 27) = true
  rw [Bool.and_eq_true]
  constructor
  · intro eq
    have exactBits : word.bv &&& 201326592#32 = 201326592#32 := congrArg U32.bv eq
    have found := (masked_eq _ _).mp exactBits
    exact ⟨found 26 (by decide) (by decide), found 27 (by decide) (by decide)⟩
  · rintro ⟨xs, os⟩
    apply U32.bv_eq_imp_eq
    apply (masked_eq _ _).mpr
    intro i bounded enabled
    have selected : i = 26 ∨ i = 27 := by simpa only [selects i bounded, decide_eq_true_eq] using enabled
    rcases selected with same | same
    · simpa only [same] using xs
    · simpa only [same] using os

private theorem xcr0_test (snapshot : Snapshot) :
    (snapshot.xcr0 &&& 230#u64 = 230#u64) ↔ xcr0Available snapshot = true := by
  let word := snapshot.xcr0
  have selects (i : Nat) (bounded : i < 64) :
      (230#u64).bv.getLsbD i = decide (i = 1 ∨ i = 2 ∨ i = 5 ∨ i = 6 ∨ i = 7) := by
    interval_cases i <;> decide +kernel
  change (word &&& 230#u64 = 230#u64) ↔
    (word.bv.getLsbD 1 && word.bv.getLsbD 2 && word.bv.getLsbD 5 &&
      word.bv.getLsbD 6 && word.bv.getLsbD 7) = true
  simp only [Bool.and_eq_true]
  constructor
  · intro eq
    have exactBits : word.bv &&& 230#64 = 230#64 := congrArg U64.bv eq
    have found := (masked_eq _ _).mp exactBits
    exact ⟨⟨⟨⟨found 1 (by decide) (by decide), found 2 (by decide) (by decide)⟩,
      found 5 (by decide) (by decide)⟩, found 6 (by decide) (by decide)⟩,
      found 7 (by decide) (by decide)⟩
  · rintro ⟨⟨⟨⟨one, two⟩, five⟩, six⟩, seven⟩
    apply U64.bv_eq_imp_eq
    apply (masked_eq _ _).mpr
    intro i bounded enabled
    have selected : i = 1 ∨ i = 2 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
      simpa only [selects i bounded, decide_eq_true_eq] using enabled
    rcases selected with same | same | same | same | same
    · simpa only [same] using one
    · simpa only [same] using two
    · simpa only [same] using five
    · simpa only [same] using six
    · simpa only [same] using seven

theorem detect_refines : DetectRefines := by
  intro snapshot
  have shift16 : (1#u32 <<< 16#i32 : Result U32) = Result.ok 65536#u32 := rfl
  have shift10 : (1#u32 <<< 10#i32 : Result U32) = Result.ok 1024#u32 := rfl
  have shift26 : (3#u32 <<< 26#i32 : Result U32) = Result.ok 201326592#u32 := rfl
  have flag16 := word_test snapshot.leaf7.ebx 65536#u32 16 (by decide) (by
    intro i bounded
    interval_cases i <;> decide +kernel)
  have flag10 := word_test snapshot.leaf7.ecx 1024#u32 10 (by decide) (by
    intro i bounded
    interval_cases i <;> decide +kernel)
  have support (cpu os : Bool) :
      bulksketch.backend.detect.vpclmul512_supported cpu os = Result.ok (cpu && os) :=
    supported_refines cpu os
  have osBits : decide (snapshot.xcr0 &&& 230#u64 = 230#u64) = xcr0Available snapshot := by
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using xcr0_test snapshot
  simp only [bulksketch.backend.x86_vpclmul512.detect, cpuid, cpuidCount, true_and, ite_true,
    bind_ok, shift16, shift10, shift26, lift, flag16, flag10]
  by_cases saved : snapshot.leaf1.ecx &&& 201326592#u32 = 201326592#u32
  · have xsave := (xsave_test snapshot).mp saved
    simp only [saved, xgetbv, true_and, ite_true, bind_ok, lift, osBits, xsave, Bool.true_and]
    cases enabled : snapshot.leaf7.ebx.bv.getLsbD 16 <;>
      simp only [enabled, cpuAvailable, Bool.false_eq_true, ite_false, ite_true, bind_ok,
        Bool.false_and, Bool.true_and, Bool.and_false, support]
  · have xsave : xsaveAvailable snapshot = false := by
      cases bit : xsaveAvailable snapshot with
      | false => rfl
      | true => exact False.elim (saved ((xsave_test snapshot).mpr bit))
    simp only [saved, ite_false, bind_ok, xsave, Bool.false_and]
    cases enabled : snapshot.leaf7.ebx.bv.getLsbD 16 <;>
      simp only [enabled, cpuAvailable, Bool.false_eq_true, ite_false, ite_true, bind_ok,
        Bool.false_and, Bool.true_and, Bool.and_false, support]

end BulksketchBridge.X86FeatureDetect
