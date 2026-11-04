import BulksketchProofs.Field.ReductionSpec
import BulksketchProofs.Resource.WorkMeterSpec
import BulksketchProofs.Generated.Reduce

/-! Frozen proposition definitions: no proof holes or assumed application theorems.
The solutions must have these exact elaborated types. -/

namespace BulksketchProofs.Challenges

def reductionCertificate : Prop :=
  ∀ (low high : BitVec 64),
    Field.join128 low high =
      (Generated.reduceGf64 low high).setWidth 128 ^^^
        Field.modulusMultiple128 (high ^^^ Field.overflow64 high)

def generatedExpressionMatchesModel : Prop :=
  ∀ (low high : BitVec 64), Generated.reduceGf64 low high = Field.reduceFold64 low high

def remainderHasCanonicalDegree : Prop :=
  ∀ (low high : BitVec 64) (index : Nat), 64 ≤ index →
    ((Generated.reduceGf64 low high).setWidth 128).getLsbD index = false

def reductionCertificateIsUnique : Prop :=
  ∀ (low high remainder quotient : BitVec 64),
    Field.join128 low high = remainder.setWidth 128 ^^^ Field.modulusMultiple128 quotient →
    quotient = high ^^^ Field.overflow64 high ∧ remainder = Generated.reduceGf64 low high

def reductionIsXorLinear : Prop :=
  ∀ (low₁ high₁ low₂ high₂ : BitVec 64),
    Generated.reduceGf64 (low₁ ^^^ low₂) (high₁ ^^^ high₂) =
      Generated.reduceGf64 low₁ high₁ ^^^ Generated.reduceGf64 low₂ high₂

def chargeSucceedsExactly : Prop :=
  ∀ (meter : Resource.WorkMeter) (amount : UInt64),
    (meter.charge amount).2 = true ↔
      meter.exhausted = false ∧ meter.used.toNat + amount.toNat ≤ meter.limit.toNat

def deniedChargePreservesUsed : Prop :=
  ∀ (meter : Resource.WorkMeter) (amount : UInt64),
    (meter.charge amount).2 = false → (meter.charge amount).1.used = meter.used

def boundedAccountingIsPreserved : Prop :=
  ∀ (meter : Resource.WorkMeter) (amount : UInt64),
    meter.Bounded → (meter.charge amount).1.Bounded

def successfulSequenceAccountsExactly : Prop :=
  ∀ (meter : Resource.WorkMeter) (amounts : List UInt64),
    (meter.chargeAll amounts).2 = true →
      (meter.chargeAll amounts).1.used.toNat =
        meter.used.toNat + (amounts.map UInt64.toNat).sum

def exhaustedMeterRejectsEveryCharge : Prop :=
  ∀ (meter : Resource.WorkMeter) (amount : UInt64),
    meter.exhausted = true → meter.charge amount = (meter, false)

end BulksketchProofs.Challenges
