import Arithmetic.AvxRecurrenceEntryGenerated
import BulksketchBridge.AvxRecurrenceComplete

namespace BulksketchBridge.AvxRecurrence

open Aeneas.Std AvxSquareRuntime AvxSquare
open bulksketch.backend.contract bulksketch.backend.portable
open bulksketch.backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels
  (odd_recurrence_matches)

/-- The original backend trait dispatch uses the original AVX recurrence
at width 64 and the original scalar default under the Portable dictionary
at every other width. -/
def ActualNativeAvxRecurrenceEntry : Prop :=
  ∀ (loadModel : Load)
    (portableModel : {F : Type} → bulksketch.field.BinaryField F → BulkKernels Portable F)
    {F : Type} (field : bulksketch.field.BinaryField F) (bits : U32) (odd squared : Slice U64),
    field.BITS = .ok bits →
    odd_recurrence_matches loadModel portableModel field odd squared =
      if bits = 64#u32 then bulksketch.backend.x86_vpclmul512.odd_recurrence_matches loadModel odd squared
      else BulkKernels.odd_recurrence_matches.default (portableModel field) odd squared

theorem native_avx_recurrence_entry : ActualNativeAvxRecurrenceEntry := by
  intro loadModel portableModel F field bits odd squared bitWidth
  by_cases width : bits = 64#u32
  · rw [width] at bitWidth
    simp only [odd_recurrence_matches, bitWidth, bind_ok, bne_self_eq_false,
      Bool.false_eq_true, ite_false, width, ite_true]
  · have other : (bits != 64#u32) = true := bne_iff_ne.mpr width
    simp only [odd_recurrence_matches, bitWidth, bind_ok, other, ite_true, width, ite_false]

/-- Under the GF64 dictionary, the original trait method compares the
exact scalar continuation through its checked AVX implementation. -/
def ActualNativeAvxRecurrenceEntryGf64 : Prop :=
  ∀ (loadModel : Load), LoadLaw loadModel →
  ∀ (portableModel : {F : Type} → bulksketch.field.BinaryField F → BulkKernels Portable F)
    (odd squared : Slice U64),
    0 < squared.length →
    ∃ answer : Bool,
      odd_recurrence_matches loadModel portableModel OddRecurrence.fieldDictionary odd squared = .ok answer ∧
      (answer = true ↔ OddRecurrence.continuationMatches odd squared)

theorem native_avx_recurrence_entry_gf64 : ActualNativeAvxRecurrenceEntryGf64 := by
  intro loadModel loadLaw portableModel odd squared positive
  have bits : OddRecurrence.fieldDictionary.BITS = .ok 64#u32 := by
    change Result.ok bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS = _
    rw [bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS]
  have dispatch := native_avx_recurrence_entry loadModel portableModel OddRecurrence.fieldDictionary
    64#u32 odd squared bits
  rw [dispatch, ite_eq_left rfl]
  exact native_avx_recurrence loadModel loadLaw odd squared positive

#print axioms native_avx_recurrence_entry
#print axioms native_avx_recurrence_entry_gf64

end BulksketchBridge.AvxRecurrence
