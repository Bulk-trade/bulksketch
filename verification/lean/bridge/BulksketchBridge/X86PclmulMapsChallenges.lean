import Arithmetic.X86PclmulNextGenerated
import BulksketchBridge.MapsQuadraticSpec
import BulksketchProofs.Field.PeriodSpec

namespace BulksketchBridge.X86PclmulMapsChallenges

open Aeneas.Std BulksketchProofs.Field.Period

abbrev dictionary := bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField

def FrobeniusRefines : Prop :=
  ∀ (input : U64) (power : U32),
    bulksketch.backend.x86_pclmul.frobenius dictionary input power =
      Result.ok (⟨iterateSquare power.val input.bv⟩ : U64)

def FrobeniusEntryRefines : Prop :=
  ∀ (input : U64) (power : U32),
    bulksketch.backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic.frobenius
      dictionary input power = Result.ok (⟨iterateSquare power.val input.bv⟩ : U64)

def SolveQuadraticRefines : Prop :=
  ∀ input : U64,
    bulksketch.backend.x86_pclmul.solve_quadratic dictionary input =
      Result.ok (MapsQuadratic.expectedSolution input)

def SolveQuadraticEntryRefines : Prop :=
  ∀ input : U64,
    bulksketch.backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic.solve_quadratic
      dictionary input = Result.ok (MapsQuadratic.expectedSolution input)

end BulksketchBridge.X86PclmulMapsChallenges
