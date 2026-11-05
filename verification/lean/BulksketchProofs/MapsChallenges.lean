import BulksketchProofs.Field.MapsSpec

namespace BulksketchProofs.MapsChallenges

def columnsMatchSourceRows : Prop :=
  ∀ (index output : Fin 64), (Field.Maps.column index.val).getLsbD output.val =
    ((Field.Maps.rows[output.val]?).getD 0).getLsbD index.val

def absoluteTraceMatchesSelector : Prop :=
  ∀ input : BitVec 64, Field.Maps.absoluteTrace input = Field.Maps.traceWord input

def traceIsTheConjugateSum : Prop :=
  ∀ input : BitVec 64, Field.Maps.absoluteTrace input = Field.Maps.traceSumPrefix 64 input

def allChunkEntriesMatchMatrix : Prop :=
  ∀ (row : Fin 16) (nibble : BitVec 4), Field.Maps.chunkValue row.val nibble =
    Field.Maps.quadraticValue (nibble.setWidth 64 <<< (4 * row.val))

def chunkLookupMatchesMatrixForEveryWord : Prop :=
  ∀ input : BitVec 64, Field.Maps.quadraticChunkValue input = Field.Maps.quadraticValue input

def quadraticRightInverseProjection : Prop :=
  ∀ input : BitVec 64, Field.Maps.quadratic (Field.Maps.quadraticValue input) =
    Field.Maps.traceProjection input

def quadraticLeftInverseProjection : Prop :=
  ∀ input : BitVec 64, Field.Maps.quadraticValue (Field.Maps.quadratic input) =
    Field.Maps.normalizedProjection input

def quadraticMapHasZeroTrace : Prop :=
  ∀ input : BitVec 64, Field.Maps.traceBit (Field.Maps.quadratic input) = false

def chosenSolutionHasZeroFreeBit : Prop :=
  ∀ input : BitVec 64, (Field.Maps.quadraticValue input).getLsbD 0 = false

def quadraticSolutionsExactlyTraceZero : Prop :=
  ∀ input : BitVec 64, (∃ solution, Field.Maps.quadratic solution = input) ↔
    Field.Maps.traceBit input = false

def normalizedSolutionIsUnique : Prop :=
  ∀ (input solution : BitVec 64), Field.Maps.quadratic solution = input →
    solution.getLsbD 0 = false → solution = Field.Maps.quadraticValue input

end BulksketchProofs.MapsChallenges
