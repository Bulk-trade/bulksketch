import Arithmetic.NewtonGuardGenerated
import BulksketchBridge.InverseFieldSpec
import BulksketchBridge.SquareSpec

namespace BulksketchBridge.NewtonGuardResidual

open Aeneas.Std bulksketch.backend.contract bulksketch.decode.deg34
open BulksketchProofs.Field

abbrev fieldDictionary := bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField
abbrev mulWord := Inverse.multiplyNativeWord
abbrev squareWord := Square.expectedWord
abbrev RangeU32 := core.ops.range.Range U32
abbrev RangeUsize := core.ops.range.Range Usize
abbrev Inclusive := core.ops.range.RangeInclusive Usize

/-- The guard reads only multiplication and square from the field callbacks. -/
def CorrectArithmetic {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) : Prop :=
  (∀ left right, kernels.ArithmeticInst.mul left right = bulksketch.field.gf64.mul fieldDictionary left right) ∧
  (∀ input, kernels.ArithmeticInst.square input = bulksketch.field.gf64.square fieldDictionary input)

/-- The represented guard powers are positive and below 16. -/
def squaresFor (power : Nat) : Nat := (BitVec.ofNat 4 power).ctz.toNat

def observationIndex (power : Nat) : Nat := (power >>> squaresFor power) / 2

def observedWord (odd : Slice U64) (power : Nat) : U64 :=
  ⟨Period.iterateSquare (squaresFor power) odd[observationIndex power]!.bv⟩

def lagTerm (odd out : Slice U64) (degree exponent lag : Nat) : U64 :=
  mulWord out[degree - lag]! (observedWord odd (exponent - lag))

/-- XOR accumulation for the remaining ascending lags. -/
def residualFrom (odd out : Slice U64) (degree exponent lag : Nat) (accumulator : U64) : Nat → U64
  | 0 => accumulator
  | count + 1 => residualFrom odd out degree exponent (lag + 1)
      (accumulator ^^^ lagTerm odd out degree exponent lag) count

def residualWord (odd out : Slice U64) (denominator : U64) (degree index : Nat) : U64 :=
  residualFrom odd out degree (2 * index + 1) 1 (mulWord denominator odd[index]!) degree

/-- A failed residual stops the scan at its first nonzero equation. -/
def residualChecks (odd out : Slice U64) (denominator : U64) (degree index : Nat) : Nat → Bool
  | 0 => true
  | count + 1 => decide (residualWord odd out denominator degree index = 0#u64) &&
      residualChecks odd out denominator degree (index + 1) count

def residualOK (odd out : Slice U64) (denominator : U64) (degree : Nat) : Bool :=
  residualChecks odd out denominator degree degree (min odd.length (degree + 2) - degree)

def remainingLags (iter : Inclusive) : Nat :=
  if iter.exhausted then 0 else iter.«end».val + 1 - iter.start.val

structure LagBounds (iter : Inclusive) (odd : Slice U64) (degree : Usize)
    (out : Slice U64) (exponent : Usize) : Prop where
  positive : 1 ≤ iter.start.val
  last : iter.«end» = degree
  exponentLower : degree.val < exponent.val
  exponentUpper : exponent.val ≤ 11
  oddBound : exponent.val / 2 < odd.length
  outBound : degree.val ≤ out.length

def ActualGuardSquareLoops : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64), CorrectArithmetic kernels →
    ∀ (iter : RangeU32) (word : U64),
      let result : U64 := ⟨Period.iterateSquare (iter.«end».val - iter.start.val) word.bv⟩
      guard_loop0_loop0_loop0 fieldDictionary kernels iter word = .ok result ∧
      guard_loop1_loop0_loop0 fieldDictionary kernels iter word = .ok result

def ActualGuardLagLoops : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64), CorrectArithmetic kernels →
    ∀ (iter : Inclusive) (odd : Slice U64) (degree : Usize) (out : Slice U64)
      (exponent : Usize) (accumulator : U64), LagBounds iter odd degree out exponent →
      let result := residualFrom odd out degree.val exponent.val iter.start.val accumulator (remainingLags iter)
      guard_loop0_loop0 fieldDictionary kernels iter odd degree out exponent accumulator = .ok result ∧
      guard_loop1_loop0 fieldDictionary kernels iter odd degree out exponent accumulator = .ok result

def ActualGuardResidualLoops : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64), CorrectArithmetic kernels →
    ∀ (iter : RangeUsize) (odd : Slice U64) (degree : Usize) (out : Slice U64) (denominator : U64),
      (degree.val = 3 ∨ degree.val = 4) → degree.val ≤ iter.start.val →
      iter.«end».val ≤ min odd.length (degree.val + 2) → degree.val ≤ out.length →
      let result := residualChecks odd out denominator degree.val iter.start.val (iter.«end».val - iter.start.val)
      guard_loop0 fieldDictionary kernels iter odd degree out denominator = .ok result ∧
      guard_loop1 fieldDictionary kernels iter odd degree out denominator = .ok result

end BulksketchBridge.NewtonGuardResidual
