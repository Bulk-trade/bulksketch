import BulksketchProofs.Field.PeriodSpec
import BulksketchProofs.Generated.FieldTables

namespace BulksketchProofs.Field.Maps

abbrev rows : List (BitVec 64) := Generated.FieldTables.quadraticRows
abbrev chunks : List (List (BitVec 64)) := Generated.FieldTables.quadraticChunks

def traceBit (input : BitVec 64) : Bool := input.getLsbD 61 ^^ input.getLsbD 63
def traceWord (input : BitVec 64) : BitVec 64 := if traceBit input then 1 else 0

/-- Horner evaluation of the sum of the first `count` polynomial conjugates. -/
def tracePrefix : Nat → BitVec 64 → BitVec 64
  | 0, _ => 0
  | count + 1, input => Period.squareWord (tracePrefix count input) ^^^ input

def traceSumPrefix : Nat → BitVec 64 → BitVec 64
  | 0, _ => 0
  | count + 1, input => traceSumPrefix count input ^^^ Period.iterateSquare count input

def absoluteTrace (input : BitVec 64) : BitVec 64 := tracePrefix 64 input

/-- Untrusted generated transpose data; a separate certificate checks all bits. -/
def column (index : Nat) : BitVec 64 :=
  (Generated.FieldTables.quadraticColumns[index]?).getD 0

/-- Independent row-matrix map, evaluated as its selected polynomial columns. -/
def quadraticPrefix (input : BitVec 64) : Nat → BitVec 64
  | 0 => 0
  | count + 1 => quadraticPrefix input count ^^^
      (if input.getLsbD count then column count else 0)

def quadraticValue (input : BitVec 64) : BitVec 64 := quadraticPrefix input 64

def chunkValue (row : Nat) (nibble : BitVec 4) : BitVec 64 :=
  (((chunks[row]?).getD [])[nibble.toNat]?).getD 0

def chunkPrefix (input : BitVec 64) : Nat → BitVec 64
  | 0 => 0
  | count + 1 => chunkPrefix input count ^^^
      chunkValue count ((input >>> (4 * count)).setWidth 4)

def quadraticChunkValue (input : BitVec 64) : BitVec 64 := chunkPrefix input 16

def quadratic (input : BitVec 64) : BitVec 64 := Period.squareWord input ^^^ input

def traceProjection (input : BitVec 64) : BitVec 64 :=
  input ^^^ (if traceBit input then (1 : BitVec 64) <<< 63 else 0)

def normalizedProjection (input : BitVec 64) : BitVec 64 :=
  input ^^^ (if input.getLsbD 0 then 1 else 0)

end BulksketchProofs.Field.Maps
