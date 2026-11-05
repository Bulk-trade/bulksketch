import BulksketchBridge.FrobeniusChallenges
import BulksketchProofs.Field.PeriodSpec

/-! New algebraic-period contracts, additive to the earlier frozen source
behavior at power modulo64. No old model or challenge definition is edited. -/

namespace BulksketchBridge.FrobeniusPeriod

open Aeneas.Std

def ExistingModelMatchesCore : Prop :=
  ∀ (count : Nat) (input : BitVec 64),
    Frobenius.repeatedSquare count input =
      BulksketchProofs.Field.Period.iterateSquare count input

def ExistingModelPeriod64 : Prop :=
  ∀ input : BitVec 64, Frobenius.repeatedSquare 64 input = input

def ExistingModelModulo64 : Prop :=
  ∀ (count : Nat) (input : BitVec 64),
    Frobenius.repeatedSquare (count % 64) input = Frobenius.repeatedSquare count input

def NativeUnmoddedIteration : Prop :=
  ∀ (input : U64) (power : U32),
    bulksketch.field.gf64.frobenius
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField input power =
        Result.ok (⟨BulksketchProofs.Field.Period.iterateSquare power.val input.bv⟩ : U64)

end BulksketchBridge.FrobeniusPeriod
