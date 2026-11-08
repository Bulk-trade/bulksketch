import BulksketchBridge.DegreeProbeRuntimeRun
import BulksketchBridge.PortableEncoding

namespace BulksketchBridge.DegreeProbeRuntime

open Aeneas.Std bulksketch.backend.contract
open bulksketch.decode.degree_probe bulksketch.decode.row bulksketch.decode.scratch bulksketch.types
open bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels

@[simp] theorem encodedWords_length (shape roots : Slice U64) :
    (encodedWords shape roots).length = shape.length := by
  simp [encodedWords, Slice.length]

theorem encodedWords_slot (shape roots : Slice U64) (slot : Nat) (inside : slot < shape.length) :
    (encodedWords shape roots)[slot]! = PortableEncoding.foldColumn roots.val slot 0#u64 := by
  simp only [encodedWords, Slice.getElem!_Nat_eq, Slice.from_val]
  rw [← List.Inhabited_getElem_eq_getElem! _ _ (by simpa using inside), List.getElem_ofFn]

/-- The original default encoder with the original Portable insertion callback
supplies the exact word frame used by the long-root degree-probe verifier. -/
theorem encoding_of_portable_default {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (selectDefault : kernels.encode_nonzero = BulkKernels.encode_nonzero.default kernels)
    (insert : ∀ scratch roots, kernels.insert_nonzero scratch roots =
      insert_nonzero fieldDictionary scratch roots) : CorrectEncoding kernels := by
  intro scratch roots
  obtain ⟨output, normal, length, values⟩ := PortableEncoding.encode_nonzero_refines K kernels insert scratch roots
  rw [selectDefault, normal]
  congr 1
  apply Slice.ext_getElem (length.trans (encodedWords_length scratch roots).symm)
  intro slot leftBound rightBound
  have inside : slot < scratch.length := length ▸ leftBound
  rw [Slice.getElem_Nat_eq output slot leftBound, Slice.getElem_Nat_eq (encodedWords scratch roots) slot rightBound,
    List.Inhabited_getElem_eq_getElem! output.val slot leftBound,
    List.Inhabited_getElem_eq_getElem! (encodedWords scratch roots).val slot rightBound,
    ← Slice.getElem!_Nat_eq output slot, ← Slice.getElem!_Nat_eq (encodedWords scratch roots) slot,
    values slot inside, encodedWords_slot scratch roots slot inside]

/-- The full paid probe transition with the original default encoder and
Portable insertion selected by the backend dictionary. -/
theorem run_portable_refines {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : Cubic.CorrectArithmetic kernels)
    (selectDefault : kernels.encode_nonzero = BulkKernels.encode_nonzero.default kernels)
    (insert : ∀ scratch roots, kernels.insert_nonzero scratch roots = insert_nonzero fieldDictionary scratch roots)
    (phase : Phase) (self : DegreeProbe) (odd : Slice U64) (budget : RowBudget)
    (workspace : RowWorkspace) (meter : WorkMeter) (admitted : Admitted phase self odd workspace) :
    DegreeProbe.run fieldDictionary kernels self odd budget workspace meter =
      paid self workspace meter (phasePrice phase (degreeWord self) odd budget)
        (phaseResult kernels phase self odd budget workspace) :=
  run_refines kernels phase self odd budget workspace meter arithmetic
    (fun _ => encoding_of_portable_default kernels selectDefault insert) admitted

end BulksketchBridge.DegreeProbeRuntime
