import Arithmetic.X86PclmulHornerGenerated
import BulksketchBridge.MutableZipPrefix
import BulksketchBridge.PortableHornerChallenges

namespace BulksketchBridge.X86PclmulHornerChallenges

open Aeneas.Std BulksketchBridge.MutableZip PortableHornerChallenges

abbrev dictionary := bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField

/-- Empty coefficients clear the entire output. Otherwise Zip updates its
common prefix and preserves unmatched destination words. -/
def expectedOutput (coefficients points out : Slice U64) : Slice U64 :=
  match coefficients.val.reverse with
  | [] => Slice.from (List.replicate out.length 0#u64) (by simp)
  | leading :: rest => mapPrefixFrom out points (fun _ point => rest.foldl (stepWord point) leading) 0

def HornerRefines : Prop :=
  ∀ (cl : Bool) (coefficients points out : Slice U64),
    bulksketch.backend.x86_pclmul.horner cl dictionary coefficients points out =
      Result.ok (expectedOutput coefficients points out)

def HornerEntryRefines : Prop :=
  ∀ coefficients points out : Slice U64,
    bulksketch.backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractBulkKernels.horner_many
      dictionary coefficients points out =
        if out.length = points.length then Result.ok (expectedOutput coefficients points out)
        else Result.fail Error.panic

end BulksketchBridge.X86PclmulHornerChallenges
