import BulksketchBridge.DefaultWireDifference
import Arithmetic.DefaultWireDifferenceDictionariesGenerated

namespace BulksketchBridge.DefaultWireDifference

open Aeneas.Std
open bulksketch.backend.contract.BulkKernels
open bulksketch.backend.portable (Portable)
open bulksketch.backend.x86_pclmul (Pclmul)

abbrev portableKernels := @Portable.Insts.BulksketchBackendContractBulkKernels
abbrev pclmulKernels := @Pclmul.Insts.BulksketchBackendContractBulkKernels

/-- Both exact extracted backend dictionaries inherit the same source body. -/
def ActualDefaultWireDifferenceBindings : Prop :=
  ∀ {F : Type} (field : bulksketch.field.BinaryField F),
    (portableKernels field).difference = difference.default Portable F ∧
    (pclmulKernels field).difference = difference.default Pclmul F

theorem default_wire_difference_bindings : ActualDefaultWireDifferenceBindings := by
  intro F field
  exact ⟨rfl, rfl⟩

#print axioms default_wire_difference_bindings

end BulksketchBridge.DefaultWireDifference
