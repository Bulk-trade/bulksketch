import Arithmetic.Funs
import BulksketchBridge.MapsQuadraticSpec

namespace BulksketchBridge.MapsQuadraticChallenges

open Aeneas Aeneas.Std

/-- Kernel linkage of every generated row literal to the independent source data. -/
def allGeneratedRowsMatchSourceData : Prop :=
  bulksketch.field.maps.GF64_QUADRATIC.val.map (fun word => word.bv) =
    BulksketchProofs.Field.Maps.rows

/-- Kernel linkage of every generated chunk literal, retaining the16-by16 shape. -/
def allGeneratedChunksMatchSourceData : Prop :=
  bulksketch.field.quadratic_chunks.GF64_QUADRATIC_CHUNKS.val.map
    (fun row => row.val.map (fun word => word.bv)) =
      BulksketchProofs.Field.Maps.chunks

def actualRowsReturnExactSourceData : Prop :=
  ∃ output : Slice U64,
    bulksketch.field.maps.quadratic_rows
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField = Result.ok output ∧
    output.val.map (fun word => word.bv) = BulksketchProofs.Field.Maps.rows ∧
    output.val.length = 64

def actualValueMatchesAllChunkContributions : Prop :=
  ∀ input : U64,
    bulksketch.field.maps.quadratic_value
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField input =
        Result.ok (MapsQuadratic.expectedChunkWord input)

def actualValueMatchesIndependentMatrix : Prop :=
  ∀ input : U64,
    bulksketch.field.maps.quadratic_value
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField input =
        Result.ok (MapsQuadratic.expectedMatrixWord input)

def actualSolverMatchesNormalizedModel : Prop :=
  ∀ input : U64,
    bulksketch.field.maps.solve_quadratic
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField input =
        Result.ok (MapsQuadratic.expectedSolution input)

def actualSolverHasExactNormalizedSolutionMeaning : Prop :=
  ∀ input : U64, ∃ output : Option U64,
    bulksketch.field.maps.solve_quadratic
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField input = Result.ok output ∧
    match output with
    | none => BulksketchProofs.Field.Maps.traceBit input.bv = true
    | some solution =>
      BulksketchProofs.Field.Maps.quadratic solution.bv = input.bv ∧
      solution.bv.getLsbD 0 = false ∧
      ∀ other : BitVec 64,
        BulksketchProofs.Field.Maps.quadratic other = input.bv →
        other.getLsbD 0 = false → other = solution.bv

end BulksketchBridge.MapsQuadraticChallenges
