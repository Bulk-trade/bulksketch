import Arithmetic.AvxSquareRuntime
import BulksketchBridge.X86MaskedMemoryRegister

namespace Aeneas.Std.AvxEncode18Runtime

open Avx512Register BulksketchBridge.X86MaskedMemory

abbrev Bases := U64 → Result Word512

def set8Value (e7 e6 e5 e4 e3 e2 e1 e0 : I64) : Word512 :=
  unflatten fun lane => ([e0, e1, e2, e3, e4, e5, e6, e7][lane.val]!).bv

def permuteValue (indices value : Word512) : Word512 :=
  unflatten fun lane =>
    flatten value ⟨(flatten indices lane).toNat % 8, Nat.mod_lt _ (by decide)⟩

def permuteTwoValue (left indices right : Word512) : Word512 :=
  unflatten fun lane =>
    let index := (flatten indices lane).toNat % 16
    if below : index < 8 then flatten left ⟨index, below⟩
    else flatten right ⟨index - 8, by have := Nat.mod_lt (flatten indices lane).toNat (by decide : 0 < 16); omega⟩

def maskMoveValue (src : Word512) (mask : U8) (data : Word512) : Word512 :=
  unflatten fun lane => if mask.bv.getLsbD lane.val then flatten data lane else flatten src lane

def set8 (e7 e6 e5 e4 e3 e2 e1 e0 : I64) : Result Word512 :=
  .ok (set8Value e7 e6 e5 e4 e3 e2 e1 e0)

def permute (indices value : Word512) : Result Word512 := .ok (permuteValue indices value)

def permuteTwo (left indices right : Word512) : Result Word512 := .ok (permuteTwoValue left indices right)

def maskMove (src : Word512) (mask : U8) (data : Word512) : Result Word512 :=
  .ok (maskMoveValue src mask data)

end Aeneas.Std.AvxEncode18Runtime
