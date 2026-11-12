import Arithmetic.FrobeniusConstGenerated
import BulksketchProofs.Field.PeriodSpec

/-! Full-word meaning of the original x86-visible compile-time square. This is
not a replacement implementation: the fixed challenge names the actual
unaltered generated body and normal return is a conclusion for every U64. -/

namespace BulksketchBridge.FrobeniusConst

open Aeneas.Std

def polynomial : BitVec 128 := ((1 : BitVec 128) <<< 64) ||| (27 : BitVec 128)

def spreadPrefix (input : BitVec 64) : Nat → BitVec 128
  | 0 => (0 : BitVec 128)
  | count + 1 => spreadPrefix input count ^^^
      (if input.getLsbD count then ((1 : BitVec 128) <<< (2 * count)) else (0 : BitVec 128))

def divisionStep (input : BitVec 128) (index : Nat) : BitVec 128 :=
  if input.getLsbD index then input ^^^ (polynomial <<< (index - 64)) else input

def divisionPrefix (input : BitVec 128) : Nat → BitVec 128
  | 0 => input
  | count + 1 => divisionStep (divisionPrefix input count) (127 - count)

def quotientPrefix (input : BitVec 128) : Nat → BitVec 64
  | 0 => (0 : BitVec 64)
  | count + 1 => quotientPrefix input count ^^^
      (if (divisionPrefix input count).getLsbD (127 - count)
       then (1 : BitVec 64) <<< (63 - count) else (0 : BitVec 64))

end BulksketchBridge.FrobeniusConst
