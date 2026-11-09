import Arithmetic.AvxEncode18Generated
import BulksketchBridge.AvxHornerInner

namespace BulksketchBridge.AvxEncode18

open Aeneas Aeneas.Std Aeneas.Std.Avx512Register Aeneas.Std.AvxEncode18Runtime
open X86MaskedMemory Avx512RegisterChallenges Algebra.Gf64
open bulksketch.backend.x86_vpclmul512

set_option maxRecDepth 4096
set_option maxHeartbeats 2500000

abbrev Triple := Word512 × Word512 × Word512

def schedule (id : U64) (base : Word512) : Triple :=
  let x := AvxHorner.splat id
  let first := productsReduced
    (maskMoveValue x 32#u8 (permuteValue (set8Value 2#i64 2#i64 2#i64 2#i64 2#i64 2#i64 2#i64 2#i64) base))
    (maskMoveValue base 32#u8 (permuteValue (set8Value 3#i64 3#i64 3#i64 3#i64 3#i64 3#i64 3#i64 3#i64) base))
  let second := productsReduced
    (permuteValue (set8Value 5#i64 0#i64 2#i64 1#i64 0#i64 1#i64 0#i64 0#i64) first)
    (permuteValue (set8Value 5#i64 4#i64 3#i64 3#i64 3#i64 2#i64 2#i64 1#i64) base)
  let right := maskMoveValue
    (permuteValue (set8Value 5#i64 5#i64 5#i64 0#i64 3#i64 3#i64 3#i64 2#i64) base)
    16#u8 (permuteValue (set8Value 5#i64 5#i64 5#i64 5#i64 5#i64 5#i64 5#i64 5#i64) first)
  let third := productsReduced
    (permuteValue (set8Value 7#i64 7#i64 7#i64 0#i64 2#i64 1#i64 0#i64 0#i64) second) right
  let low := permuteTwoValue first (set8Value 0#i64 10#i64 9#i64 2#i64 8#i64 1#i64 0#i64 0#i64) second
  let low := permuteTwoValue low (set8Value 8#i64 6#i64 5#i64 4#i64 3#i64 2#i64 1#i64 0#i64) third
  let low := maskMoveValue low 1#u8 x
  let high := permuteTwoValue first (set8Value 0#i64 0#i64 0#i64 13#i64 0#i64 12#i64 11#i64 3#i64) second
  let high := permuteTwoValue high (set8Value 12#i64 11#i64 10#i64 4#i64 9#i64 2#i64 1#i64 0#i64) third
  let tail := permuteTwoValue first (set8Value 0#i64 0#i64 0#i64 0#i64 0#i64 0#i64 14#i64 4#i64) second
  (low, high, tail)

theorem schedule_normal (baseModel : Bases) (id : U64) (base : Word512)
    (lookup : baseModel id = .ok base) :
    powers_18 baseModel id = .ok (schedule id base) := by
  have broadcast := AvxHorner.broadcast_normal id
  have signed :
      (core.num.I64.from_le_bytes (core.num.U64.to_le_bytes id)).bv = id.bv := by
    simp only [X86PclmulRuntime.unsignedBytes, X86PclmulRuntime.signedFromBytes, bind_ok,
      Avx512Register.broadcast] at broadcast
    exact congrFun (congrFun (Result.ok_injective broadcast) 0) false
  have mul (a b : Word512) : multiply true a b = .ok (productsReduced a b) :=
    Avx512Register.multiply_refines true a b
  simp only [powers_18, X86PclmulRuntime.unsignedBytes, X86PclmulRuntime.signedFromBytes,
    Avx512Register.broadcast, signed, bind_ok, lookup, set8, permute, maskMove, permuteTwo, mul, schedule]
  rfl

/-- The unresolved source table slot supplies the first seven Frobenius
powers, followed by a zero padding lane. -/
def BasesLaw (baseModel : Bases) : Prop :=
  ∀ id : U64, ∃ base, baseModel id = .ok base ∧
    ∀ lane : Fin 8,
      toField (flatten base lane) =
        if lane.val < 7 then toField id.bv ^ (2 ^ (lane.val + 1)) else 0

def rowLane (registers : Triple) (i : Fin 18) : BitVec 64 :=
  if low : i.val < 8 then flatten registers.1 ⟨i.val, low⟩
  else if high : i.val < 16 then flatten registers.2.1 ⟨i.val - 8, by omega⟩
  else flatten registers.2.2 ⟨i.val - 16, by omega⟩

theorem flatten_product (a b : Word512) (lane : Fin 8) :
    flatten (productsReduced a b) lane = multiplyWord (flatten a lane) (flatten b lane) := rfl

@[simp] theorem flatten_splat (id : U64) (lane : Fin 8) :
    flatten (AvxHorner.splat id) lane = id.bv := rfl

abbrev LaneVector (α : Type) := Fin 8 → α
abbrev LaneTriple (α : Type) := LaneVector α × LaneVector α × LaneVector α

def laneMul {α : Type} (mul : α → α → α) (a b : LaneVector α) : LaneVector α :=
  fun lane => mul (a lane) (b lane)

def laneMask {α : Type} (src : LaneVector α) (mask : U8) (data : LaneVector α) : LaneVector α :=
  fun lane => if mask.bv.getLsbD lane.val then data lane else src lane

def lanePermute {α : Type} (indices : Word512) (value : LaneVector α) : LaneVector α :=
  fun lane => value ⟨(flatten indices lane).toNat % 8, Nat.mod_lt _ (by decide)⟩

def lanePermuteTwo {α : Type} (left : LaneVector α) (indices : Word512) (right : LaneVector α) : LaneVector α :=
  fun lane =>
    let index := (flatten indices lane).toNat % 16
    if below : index < 8 then left ⟨index, below⟩
    else right ⟨index - 8, by have := Nat.mod_lt (flatten indices lane).toNat (by decide : 0 < 16); omega⟩

def laneSchedule {α : Type} (mul : α → α → α) (x base : LaneVector α) : LaneTriple α :=
  let first := laneMul mul
    (laneMask x 32#u8 (lanePermute (set8Value 2#i64 2#i64 2#i64 2#i64 2#i64 2#i64 2#i64 2#i64) base))
    (laneMask base 32#u8 (lanePermute (set8Value 3#i64 3#i64 3#i64 3#i64 3#i64 3#i64 3#i64 3#i64) base))
  let second := laneMul mul
    (lanePermute (set8Value 5#i64 0#i64 2#i64 1#i64 0#i64 1#i64 0#i64 0#i64) first)
    (lanePermute (set8Value 5#i64 4#i64 3#i64 3#i64 3#i64 2#i64 2#i64 1#i64) base)
  let right := laneMask
    (lanePermute (set8Value 5#i64 5#i64 5#i64 0#i64 3#i64 3#i64 3#i64 2#i64) base)
    16#u8 (lanePermute (set8Value 5#i64 5#i64 5#i64 5#i64 5#i64 5#i64 5#i64 5#i64) first)
  let third := laneMul mul
    (lanePermute (set8Value 7#i64 7#i64 7#i64 0#i64 2#i64 1#i64 0#i64 0#i64) second) right
  let low := lanePermuteTwo first (set8Value 0#i64 10#i64 9#i64 2#i64 8#i64 1#i64 0#i64 0#i64) second
  let low := lanePermuteTwo low (set8Value 8#i64 6#i64 5#i64 4#i64 3#i64 2#i64 1#i64 0#i64) third
  let low := laneMask low 1#u8 x
  let high := lanePermuteTwo first (set8Value 0#i64 0#i64 0#i64 13#i64 0#i64 12#i64 11#i64 3#i64) second
  let high := lanePermuteTwo high (set8Value 12#i64 11#i64 10#i64 4#i64 9#i64 2#i64 1#i64 0#i64) third
  let tail := lanePermuteTwo first (set8Value 0#i64 0#i64 0#i64 0#i64 0#i64 0#i64 14#i64 4#i64) second
  (low, high, tail)

def laneRow {α : Type} (values : LaneTriple α) (i : Fin 18) : α :=
  if low : i.val < 8 then values.1 ⟨i.val, low⟩
  else if high : i.val < 16 then values.2.1 ⟨i.val - 8, by omega⟩
  else values.2.2 ⟨i.val - 16, by omega⟩

def flattenTriple (values : Triple) : LaneTriple (BitVec 64) :=
  (flatten values.1, flatten values.2.1, flatten values.2.2)

@[simp] private theorem flatten_mask (a : Word512) (mask : U8) (b : Word512) :
    flatten (maskMoveValue a mask b) = laneMask (flatten a) mask (flatten b) := by
  unfold maskMoveValue laneMask
  rw [flatten_unflatten]

@[simp] private theorem flatten_permute (indices value : Word512) :
    flatten (permuteValue indices value) = lanePermute indices (flatten value) := by
  unfold permuteValue lanePermute
  rw [flatten_unflatten]

@[simp] private theorem flatten_permute_two (a indices b : Word512) :
    flatten (permuteTwoValue a indices b) = lanePermuteTwo (flatten a) indices (flatten b) := by
  unfold permuteTwoValue lanePermuteTwo
  rw [flatten_unflatten]

@[simp] private theorem flatten_mul (a b : Word512) :
    flatten (productsReduced a b) = laneMul multiplyWord (flatten a) (flatten b) := by
  funext lane
  exact flatten_product a b lane

private theorem schedule_lanes (id : U64) (base : Word512) :
    flattenTriple (schedule id base) = laneSchedule multiplyWord (fun _ => id.bv) (flatten base) := by
  have spread : flatten (AvxHorner.splat id) = fun _ => id.bv := by funext lane; rfl
  simp only [flattenTriple, schedule, laneSchedule, flatten_mask, flatten_permute, flatten_permute_two, flatten_mul, spread]

def mapLanes {α β : Type} (f : α → β) (lanes : LaneVector α) : LaneVector β :=
  fun lane => f (lanes lane)

def mapTriple {α β : Type} (f : α → β) (values : LaneTriple α) : LaneTriple β :=
  (mapLanes f values.1, mapLanes f values.2.1, mapLanes f values.2.2)

@[simp] private theorem map_lane_mul {α β : Type} (f : α → β) (mul : α → α → α) (times : β → β → β)
    (preserves : ∀ a b, f (mul a b) = times (f a) (f b)) (a b : LaneVector α) :
    mapLanes f (laneMul mul a b) = laneMul times (mapLanes f a) (mapLanes f b) := by
  funext lane
  exact preserves _ _

@[simp] private theorem map_lane_mask {α β : Type} (f : α → β) (src : LaneVector α) (mask : U8) (data : LaneVector α) :
    mapLanes f (laneMask src mask data) = laneMask (mapLanes f src) mask (mapLanes f data) := by
  funext lane
  unfold mapLanes laneMask
  split <;> rfl

@[simp] private theorem map_lane_permute {α β : Type} (f : α → β) (indices : Word512) (value : LaneVector α) :
    mapLanes f (lanePermute indices value) = lanePermute indices (mapLanes f value) := rfl

@[simp] private theorem map_lane_permute_two {α β : Type} (f : α → β) (a : LaneVector α) (indices : Word512) (b : LaneVector α) :
    mapLanes f (lanePermuteTwo a indices b) = lanePermuteTwo (mapLanes f a) indices (mapLanes f b) := by
  funext lane
  unfold mapLanes lanePermuteTwo
  dsimp only
  split <;> rfl

private theorem map_schedule {α β : Type} (f : α → β) (mul : α → α → α) (times : β → β → β)
    (preserves : ∀ a b, f (mul a b) = times (f a) (f b)) (x base : LaneVector α) :
    mapTriple f (laneSchedule mul x base) =
      laneSchedule times (mapLanes f x) (mapLanes f base) := by
  simp only [mapTriple, laneSchedule, map_lane_mul f mul times preserves,
    map_lane_mask, map_lane_permute, map_lane_permute_two]

private theorem map_row {α β : Type} (f : α → β) (values : LaneTriple α) (i : Fin 18) :
    laneRow (mapTriple f values) i = f (laneRow values i) := by
  unfold laneRow mapTriple mapLanes
  split <;> try rfl
  split <;> rfl

def exponentMul (a b : Option Nat) : Option Nat := a.bind (fun a => b.map (fun b => a + b))

def exponentBasis : LaneVector (Option Nat) :=
  fun lane => if lane.val < 7 then some (2 ^ (lane.val + 1)) else none

noncomputable def exponentValue (x : Field) : Option Nat → Field
  | none => 0
  | some e => x ^ e

private theorem exponent_mul (x : Field) (a b : Option Nat) :
    exponentValue x (exponentMul a b) = exponentValue x a * exponentValue x b := by
  cases a <;> cases b <;> simp [exponentValue, exponentMul, pow_add]

/-- The finite permutation and exponent schedule is checked independently
of the field values and without any finite-field enumeration. -/
theorem exponent_schedule : ∀ i : Fin 18,
    laneRow (laneSchedule exponentMul (fun _ => some 1) exponentBasis) i = some (2 * i.val + 1) := by
  decide

/-- All 18 selected lanes of the original permutation schedule compute the
ascending odd powers of the input field word. -/
theorem schedule_powers (id : U64) (base : Word512)
    (basis : ∀ lane : Fin 8, toField (flatten base lane) =
      if lane.val < 7 then toField id.bv ^ (2 ^ (lane.val + 1)) else 0) :
    ∀ i : Fin 18, toField (rowLane (schedule id base) i) = toField id.bv ^ (2 * i.val + 1) := by
  intro i
  let x := toField id.bv
  have mapX : mapLanes toField (fun _ => id.bv) = mapLanes (exponentValue x) (fun _ => some 1) := by
    funext lane
    simp [mapLanes, exponentValue, x]
  have mapBase : mapLanes toField (flatten base) = mapLanes (exponentValue x) exponentBasis := by
    funext lane
    unfold mapLanes exponentBasis
    rw [basis]
    split <;> rfl
  change toField (laneRow (flattenTriple (schedule id base)) i) = _
  rw [← map_row toField, schedule_lanes, map_schedule toField multiplyWord (· * ·) toField_mul,
    mapX, mapBase, ← map_schedule (exponentValue x) exponentMul (· * ·) (exponent_mul x),
    map_row, exponent_schedule]
  rfl

def ActualPowers18 : Prop :=
  ∀ (baseModel : Bases), BasesLaw baseModel → ∀ id : U64,
    ∃ values, powers_18 baseModel id = .ok values ∧
      ∀ i : Fin 18, toField (rowLane values i) = toField id.bv ^ (2 * i.val + 1)

theorem powers_refines : ActualPowers18 := by
  intro baseModel basis id
  obtain ⟨base, lookup, exactBasis⟩ := basis id
  exact ⟨schedule id base, schedule_normal baseModel id base lookup, schedule_powers id base exactBasis⟩

end BulksketchBridge.AvxEncode18
