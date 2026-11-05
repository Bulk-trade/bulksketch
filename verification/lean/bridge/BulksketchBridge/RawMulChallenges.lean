import BulksketchBridge.RawMulSpec

namespace BulksketchBridge.RawMulChallenges

def actualRawMultiplicationReturnsEveryBit : Prop :=
  RawMul.ReturnsCompleteProduct

def actualRawMultiplicationHasConvolutionCoefficients : Prop :=
  RawMul.ReturnsCoefficientConvolution

def actualMultiplicationHasDivisionCertificate : Prop :=
  RawMul.ReducedMultiplication

end BulksketchBridge.RawMulChallenges
