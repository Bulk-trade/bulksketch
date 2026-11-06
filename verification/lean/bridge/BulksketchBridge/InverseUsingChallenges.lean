import Arithmetic.InverseUsingGenerated
import BulksketchBridge.InverseFieldSpec

/-! Fixed contracts for the original captured-square loop and both enclosing
inversion wrappers. Source normality is a conclusion for every admitted input;
callback premises name the already-verified native arithmetic bodies. -/
namespace BulksketchBridge.InverseUsingChallenges

open Aeneas.Std

def capturedSquareReturnsEveryIteration : Prop :=
  ∀ (T1 T2 : Type)
    (multiply : core.ops.function.Fn T1 (U64 × U64) U64)
    (square : core.ops.function.Fn T2 U64 U64)
    (callback : T2),
    (∀ input, square.call callback input =
      bulksketch.field.gf64.square
        bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField input) →
    ∀ (input : U64) (power : U32),
      bulksketch.field.maps.inverse_using.closure.Insts.CoreOpsFunctionFnPairU64U32U64.call
        bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField multiply square callback
        (input, power) =
          Result.ok (⟨BulksketchProofs.Field.Period.iterateSquare power.val input.bv⟩ : U64)

def actualInverseUsingReturnsFieldInverse : Prop :=
  ∀ (T1 T2 : Type)
    (multiply : core.ops.function.Fn T1 (U64 × U64) U64)
    (square : core.ops.function.Fn T2 U64 U64)
    (mulCallback : T1) (squareCallback : T2),
    (∀ left right, multiply.call mulCallback (left, right) =
      bulksketch.field.gf64.mul
        bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField left right) →
    (∀ input, square.call squareCallback input =
      bulksketch.field.gf64.square
        bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField input) →
    ∀ input : U64,
      bulksketch.field.maps.inverse_using
        bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField multiply square input
        mulCallback squareCallback = Result.ok (Inverse.expectedFieldInverse input)

def actualInverseReturnsFieldInverse : Prop :=
  ∀ input : U64,
    bulksketch.field.maps.inverse
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField input =
        Result.ok (Inverse.expectedFieldInverse input)

end BulksketchBridge.InverseUsingChallenges
