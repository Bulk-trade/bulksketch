import BulksketchBridge.AvxSingletonLanes

namespace BulksketchBridge.AvxSingleton

open Aeneas.Std Aeneas.Std.Avx512Register Aeneas.Std.AvxEncode18Runtime

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

def scheduleSingle : List Expr :=
  let x := Expr.root
  let base := Expr.basis
  let mi : Expr := .permute (spread 0#i64) base
  let b : Expr := .mul x mi
  let a1 : Expr := .permuteTwo x unpackIndices b
  let mi1 : Expr := .permute (spread 1#i64) base
  let b1 : Expr := .mul a1 mi1
  let mi2 : Word512 := set8Value 9#i64 8#i64 1#i64 0#i64 9#i64 8#i64 1#i64 0#i64
  let a2 : Expr := .permuteTwo a1 mi2 b1
  let mi3 : Expr := .permute (spread 2#i64) base
  let b2 : Expr := .mul a2 mi3
  let mi4 : Word512 := set8Value 11#i64 10#i64 9#i64 8#i64 3#i64 2#i64 1#i64 0#i64
  let v0 : Expr := .permuteTwo a2 mi4 b2
  let mi5 : Expr := .permute (spread 3#i64) base
  let v1 : Expr := .mul v0 mi5
  let mi6 : Expr := .permute (spread 4#i64) base
  let v2 : Expr := .mul v0 mi6
  let v3 : Expr := .mul v1 mi6
  let step : Expr := .permute (spread 5#i64) base
  let v4 : Expr := .mul v0 step
  let v5 : Expr := .mul v1 step
  let v6 : Expr := .mul v2 step
  let v7 : Expr := .mul v3 step
  let step1 : Expr := .permute (spread 6#i64) base
  let mi7 : Expr := .mul v0 step1
  let mi8 : Expr := .mul v1 step1
  let mi9 : Expr := .mul v2 step1
  let mi10 : Expr := .mul v3 step1
  [v0, v1, v2, v3, v4, v5, v6, v7, mi7, mi8, mi9, mi10]

def schedule32 : List Expr :=
  let x := Expr.root
  let base := Expr.basis
  let mi : Word512 := set8Value 11#i64 10#i64 9#i64 0#i64 0#i64 0#i64 0#i64 0#i64
  let mi1 : Expr := .permuteTwo x mi base
  let mi2 : Word512 := set8Value 4#i64 3#i64 2#i64 4#i64 3#i64 2#i64 1#i64 0#i64
  let mi3 : Expr := .permute mi2 base
  let first : Expr := .mul mi1 mi3
  let mi4 : Word512 := set8Value 1#i64 0#i64 2#i64 1#i64 0#i64 1#i64 0#i64 0#i64
  let mi5 : Expr := .permute mi4 first
  let mi6 : Word512 := set8Value 4#i64 4#i64 3#i64 3#i64 3#i64 2#i64 2#i64 1#i64
  let mi7 : Expr := .permute mi6 base
  let second_low : Expr := .mul mi5 mi7
  let mi8 : Word512 := set8Value 6#i64 10#i64 0#i64 1#i64 0#i64 0#i64 3#i64 2#i64
  let mi9 : Expr := .permuteTwo first mi8 base
  let mi10 : Word512 := set8Value 4#i64 4#i64 15#i64 14#i64 14#i64 13#i64 4#i64 4#i64
  let mi11 : Expr := .permuteTwo base mi10 first
  let second_high : Expr := .mul mi9 mi11
  let mi12 : Word512 := set8Value 0#i64 9#i64 0#i64 9#i64 8#i64 0#i64 0#i64 0#i64
  let mi13 : Expr := .permuteTwo second_low mi12 first
  let mi14 : Word512 := set8Value 15#i64 15#i64 0#i64 0#i64 0#i64 4#i64 14#i64 3#i64
  let mi15 : Expr := .permuteTwo base mi14 first
  let mi16 : Word512 := set8Value 0#i64 0#i64 6#i64 6#i64 6#i64 0#i64 0#i64 0#i64
  let mi17 : Expr := .permute mi16 second_high
  let mi18 : Expr := .mask mi15 56#u8 mi17
  let third_low : Expr := .mul mi13 mi18
  let mi19 : Word512 := set8Value 0#i64 0#i64 0#i64 0#i64 8#i64 1#i64 0#i64 2#i64
  let mi20 : Expr := .permuteTwo first mi19 second_low
  let mi21 : Word512 := set8Value 0#i64 0#i64 0#i64 0#i64 15#i64 15#i64 15#i64 7#i64
  let mi22 : Expr := .permuteTwo first mi21 second_high
  let third_high : Expr := .mul mi20 mi22
  let mi23 : Word512 := set8Value 0#i64 0#i64 0#i64 10#i64 0#i64 9#i64 8#i64 0#i64
  let mi24 : Expr := .permuteTwo x mi23 first
  let mi25 : Word512 := set8Value 0#i64 2#i64 1#i64 0#i64 0#i64 0#i64 0#i64 0#i64
  let mi26 : Expr := .permute mi25 second_low
  let mi27 : Expr := .mask mi24 104#u8 mi26
  let mi28 : Word512 := set8Value 2#i64 0#i64 0#i64 0#i64 0#i64 0#i64 0#i64 0#i64
  let mi29 : Expr := .permute mi28 second_high
  let value : Expr := .mask mi27 128#u8 mi29
  let mi32 : Word512 := set8Value 0#i64 0#i64 0#i64 13#i64 0#i64 12#i64 11#i64 3#i64
  let mi33 : Expr := .permuteTwo first mi32 second_low
  let mi34 : Word512 := set8Value 1#i64 0#i64 0#i64 0#i64 0#i64 0#i64 0#i64 0#i64
  let mi35 : Expr := .permute mi34 third_low
  let mi36 : Expr := .mask mi33 136#u8 mi35
  let mi37 : Word512 := set8Value 0#i64 4#i64 3#i64 0#i64 0#i64 0#i64 0#i64 0#i64
  let mi38 : Expr := .permute mi37 second_high
  let value1 : Expr := .mask mi36 96#u8 mi38
  let mi41 : Word512 := set8Value 0#i64 0#i64 0#i64 0#i64 0#i64 15#i64 14#i64 4#i64
  let mi42 : Expr := .permuteTwo first mi41 second_low
  let mi43 : Word512 := set8Value 5#i64 4#i64 3#i64 0#i64 2#i64 0#i64 0#i64 0#i64
  let mi44 : Expr := .permute mi43 third_low
  let mi45 : Expr := .mask mi42 232#u8 mi44
  let mi46 : Word512 := set8Value 0#i64 0#i64 0#i64 0#i64 0#i64 0#i64 0#i64 0#i64
  let mi47 : Expr := .permute mi46 second_high
  let value2 : Expr := .mask mi45 16#u8 mi47
  let mi50 : Word512 := set8Value 0#i64 0#i64 0#i64 0#i64 15#i64 14#i64 5#i64 1#i64
  let mi51 : Expr := .permuteTwo second_high mi50 third_low
  let mi52 : Word512 := set8Value 3#i64 2#i64 1#i64 0#i64 0#i64 0#i64 0#i64 0#i64
  let mi53 : Expr := .permute mi52 third_high
  let value3 : Expr := .mask mi51 240#u8 mi53
  [value, value1, value2, value3]

@[simp] theorem scheduleSingle_count : scheduleSingle.length = 12 := rfl
@[simp] theorem schedule32_count : schedule32.length = 4 := rfl

theorem single_exponents : ∀ (block : Fin 12) (lane : Fin 8),
    exponents scheduleSingle[block.val]! lane = some (2 * (8 * block.val + lane.val) + 1) := by
  decide

theorem width32_exponents : ∀ (block : Fin 4) (lane : Fin 8),
    exponents schedule32[block.val]! lane = some (2 * (8 * block.val + lane.val) + 1) := by
  decide

end BulksketchBridge.AvxSingleton
