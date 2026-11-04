import BulksketchBridge.FrobeniusPeriodSpec

namespace BulksketchBridge.FrobeniusPeriodChallenges

def oldFrozenModelMatchesCoreExactly : Prop := FrobeniusPeriod.ExistingModelMatchesCore

def oldFrozenModelHasPeriod64 : Prop := FrobeniusPeriod.ExistingModelPeriod64

def oldFrozenModelIterationCountsReduceModulo64 : Prop := FrobeniusPeriod.ExistingModelModulo64

def actualNativeFrobeniusMatchesUnmoddedIteration : Prop := FrobeniusPeriod.NativeUnmoddedIteration

end BulksketchBridge.FrobeniusPeriodChallenges
