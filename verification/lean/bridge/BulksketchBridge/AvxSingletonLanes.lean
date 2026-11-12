import BulksketchBridge.AvxEncode18Powers

namespace BulksketchBridge.AvxSingleton

open Aeneas Aeneas.Std Aeneas.Std.Avx512Register Aeneas.Std.AvxEncode18Runtime
open AvxEncode18 X86MaskedMemory Algebra.Gf64 Avx512RegisterChallenges

set_option maxHeartbeats 2000000

inductive Expr where
  | root
  | basis
  | mul (left right : Expr)
  | permute (indices : Word512) (value : Expr)
  | permuteTwo (left : Expr) (indices : Word512) (right : Expr)
  | mask (src : Expr) (mask : U8) (data : Expr)
  deriving Inhabited

/-- The pinned stdarch implementation uses the exact shuffle
[0, 8, 2, 10, 4, 12, 6, 14] over the pair of input registers. -/
def unpackIndices : Word512 := set8Value 14#i64 6#i64 12#i64 4#i64 10#i64 2#i64 8#i64 0#i64

def spread (index : I64) : Word512 := fun _ _ => index.bv

def evaluate (id : U64) (base : Word512) : Expr → Word512
  | .root => AvxHorner.splat id
  | .basis => base
  | .mul a b => productsReduced (evaluate id base a) (evaluate id base b)
  | .permute indices value => permuteValue indices (evaluate id base value)
  | .permuteTwo a indices b => permuteTwoValue (evaluate id base a) indices (evaluate id base b)
  | .mask src mask data => maskMoveValue (evaluate id base src) mask (evaluate id base data)

def exponents : Expr → LaneVector (Option Nat)
  | .root => fun _ => some 1
  | .basis => exponentBasis
  | .mul a b => laneMul exponentMul (exponents a) (exponents b)
  | .permute indices value => lanePermute indices (exponents value)
  | .permuteTwo a indices b => lanePermuteTwo (exponents a) indices (exponents b)
  | .mask src mask data => laneMask (exponents src) mask (exponents data)

private theorem exponent_times (x : Field) (a b : Option Nat) :
    exponentValue x (exponentMul a b) = exponentValue x a * exponentValue x b := by
  cases a <;> cases b <;> simp [exponentValue, exponentMul, pow_add]

theorem evaluate_lanes (id : U64) (base : Word512)
    (basisLaw : ∀ lane : Fin 8, toField (flatten base lane) =
      if lane.val < 7 then toField id.bv ^ (2 ^ (lane.val + 1)) else 0) :
    ∀ (expr : Expr) (lane : Fin 8),
      toField (flatten (evaluate id base expr) lane) = exponentValue (toField id.bv) (exponents expr lane) := by
  intro expr
  induction expr with
  | root => intro lane; simp [evaluate, exponents, exponentValue]
  | basis => intro lane; rw [evaluate, basisLaw, exponents, exponentBasis]; split <;> rfl
  | mul a b ha hb =>
    intro lane
    simp only [evaluate, exponents, laneMul, flatten_product, toField_mul, ha, hb, exponent_times]
  | permute indices value ih =>
    intro lane
    simp only [evaluate, permuteValue, flatten_unflatten, exponents, lanePermute, ih]
  | permuteTwo a indices b ha hb =>
    intro lane
    simp only [evaluate, permuteTwoValue, flatten_unflatten, exponents, lanePermuteTwo]
    split <;> simp only [ha, hb]
  | mask src mask data hsrc hdata =>
    intro lane
    simp only [evaluate, maskMoveValue, flatten_unflatten, exponents, laneMask]
    split <;> simp only [hsrc, hdata]

end BulksketchBridge.AvxSingleton
