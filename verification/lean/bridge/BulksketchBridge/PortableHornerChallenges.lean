import Arithmetic.PortableHornerGenerated
import BulksketchBridge.Algebra.WordLaws

namespace BulksketchBridge.PortableHornerChallenges

open Aeneas Aeneas.Std BulksketchBridge.Algebra.Gf64

def stepWord (point value coefficient : U64) : U64 :=
  (⟨multiplyWord value.bv point.bv⟩ : U64) ^^^ coefficient

/-- Coefficients are stored in ascending order of degree. -/
def evalWord (coefficients : List U64) (point : U64) : U64 :=
  match coefficients.reverse with
  | [] => 0#u64
  | leading :: rest => rest.foldl (stepWord point) leading

def hornerRefines : Prop :=
  ∀ coefficients points out : Slice U64,
    let actual :=
      bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.horner_many
        bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField coefficients points out
    if out.length = points.length then
      ∃ result, actual = Result.ok result ∧ result.length = out.length ∧
        result.val = points.val.map (evalWord coefficients.val)
    else actual = Result.fail Error.panic

end BulksketchBridge.PortableHornerChallenges
