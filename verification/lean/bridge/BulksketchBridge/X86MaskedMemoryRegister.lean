import Arithmetic.Avx512RegisterRuntime
import BulksketchBridge.X86MaskedMemory

namespace BulksketchBridge.X86MaskedMemory

open Aeneas.Std Aeneas.Std.Avx512Register

def flatIndex (pair : Fin 4) (high : Bool) : Fin 8 :=
  ⟨2 * pair.val + (if high then 1 else 0), by split <;> omega⟩

/-- The low then high halves of each register pair occupy successive lanes. -/
def flatten (value : Word512) : Lanes :=
  fun lane => value ⟨lane.val / 2, by omega⟩ (decide (lane.val % 2 = 1))

def unflatten (value : Lanes) : Word512 := fun pair high => value (flatIndex pair high)

@[simp] theorem flatten_at (value : Word512) (pair : Fin 4) (high : Bool) :
    flatten value (flatIndex pair high) = value pair high := by
  have pairIndex : (⟨(flatIndex pair high).val / 2, by omega⟩ : Fin 4) = pair := by
    apply Fin.ext
    change (2 * pair.val + (if high then 1 else 0)) / 2 = pair.val
    split <;> omega
  have halfIndex : decide ((flatIndex pair high).val % 2 = 1) = high := by
    cases high <;> simp [flatIndex]
  simp only [flatten, pairIndex, halfIndex]

@[simp] theorem unflatten_flatten (value : Word512) : unflatten (flatten value) = value := by
  funext pair high
  exact flatten_at value pair high

@[simp] theorem flatten_unflatten (value : Lanes) : flatten (unflatten value) = value := by
  funext lane
  unfold flatten unflatten
  apply congrArg value
  apply Fin.ext
  simp only [flatIndex, decide_eq_true_eq]
  split <;> omega

/-- Read back the slice payload in ascending lane order from the new state. -/
def readPayload (mem : Memory) (base len : Nat) (admitted : len ≤ 8) : List (BitVec 64) :=
  List.ofFn fun lane : Fin len => readLane mem base ⟨lane.val, by omega⟩

def registerPayload (value : Word512) (len : Nat) (admitted : len ≤ 8) : List (BitVec 64) :=
  List.ofFn fun lane : Fin len => flatten value ⟨lane.val, by omega⟩

/-- The stateful write leaves exactly the requested register lanes in the
borrowed prefix. The caller reads the payload from the updated memory. -/
def StatefulRegisterPayload : Prop :=
  ∀ (len : Usize) (admitted : len.val ≤ 8)
    (mem : Memory) (permit : Nat → Bool) (base : Nat) (value : Word512),
    (∀ offset : Nat, offset < 8 * len.val →
      (mem (base + offset)).isSome = true ∧ permit (base + offset) = true) →
    ∃ mask : U8, ∃ updated : Memory,
      bulksketch.backend.x86_vpclmul512.mask len = Result.ok mask ∧
      store mem permit base mask.bv (flatten value) = some updated ∧
      readPayload updated base len.val admitted = registerPayload value len.val admitted ∧
      ∀ address, address < base ∨ base + 8 * len.val ≤ address → updated address = mem address

theorem store_register_payload : StatefulRegisterPayload := by
  intro len admitted mem permit base value window
  obtain ⟨mask, updated, maskNormal, write, _, frame⟩ :=
    source_mask_store_prefix len admitted mem permit base (flatten value) window
  obtain ⟨exactMask, exactNormal, _, bits⟩ := X86LaneMask.mask_refines len admitted
  have same : mask = exactMask := Result.ok_injective (maskNormal.symm.trans exactNormal)
  subst exactMask
  refine ⟨mask, updated, maskNormal, write, ?_, frame⟩
  unfold readPayload registerPayload
  apply congrArg List.ofFn
  funext lane
  apply readLane_of_bytes
  intro byte
  apply stored_byte mem updated permit base mask.bv (flatten value) write
  simp only [enabled, bits lane.val (by omega), decide_eq_true_eq]
  exact lane.isLt

end BulksketchBridge.X86MaskedMemory
