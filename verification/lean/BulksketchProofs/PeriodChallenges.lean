import BulksketchProofs.Field.PeriodSpec

namespace BulksketchProofs.PeriodChallenges

def allBasisWordsReturnAfter64Squares : Prop := Field.Period.BasisCertificate

def allWordsReturnAfter64Squares : Prop := Field.Period.SixtyFourSquaresIdentity

def allNaturalIterationCountsReduceModulo64 : Prop := Field.Period.IterationModulo64

end BulksketchProofs.PeriodChallenges
