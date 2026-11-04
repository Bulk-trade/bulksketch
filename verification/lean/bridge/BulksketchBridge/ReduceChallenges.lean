import BulksketchBridge.ReduceSpec

namespace BulksketchBridge.ReduceChallenges

def generatedGF64ReductionMatchesModel : Prop :=
  BulksketchBridge.Reduce.RefinesGF64

def generatedGF64ReductionHasDivisionCertificate : Prop :=
  BulksketchBridge.Reduce.DivisionCertificateGF64

end BulksketchBridge.ReduceChallenges
