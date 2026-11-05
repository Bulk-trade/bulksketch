import BulksketchBridge.RawMulAccumSpec

/-! Independent contracts for bounds and the original second source loop. -/

namespace BulksketchBridge.RawMulAccumChallenges

def nibbleShiftsIndicesAndCastsAreSafe : Prop :=
  BulksketchBridge.RawMulAccum.NibbleBounds

def eachOriginalBodyPreservesPrefix : Prop :=
  BulksketchBridge.RawMulAccum.BodyStep

def originalBodyStopsBeforeShift64 : Prop :=
  BulksketchBridge.RawMulAccum.TerminalBody

def everyOriginalPrefixCompletes : Prop :=
  BulksketchBridge.RawMulAccum.EveryPrefixCompletes

end BulksketchBridge.RawMulAccumChallenges
