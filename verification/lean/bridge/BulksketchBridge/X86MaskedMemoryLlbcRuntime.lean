import BulksketchBridge.X86MaskedMemoryRegister

namespace BulksketchBridge.X86MaskedMemory.Llbc

open Aeneas.Std Aeneas.Std.Avx512Register

/-- The caller supplies the view's base and fat-pointer metadata. The only
mutable view in this interpreter is the exclusive input of the store. -/
structure SliceView where
  base : Nat
  len : Usize

inductive Op where
  | live (slot : Nat)
  | dead (slot : Nat)
  | initUnit (dst : Nat)
  | reborrow (dst src : Nat) (writable : Bool)
  | copyRegister (dst src : Nat)
  | len (dst src : Nat)
  | mask (dst src : Nat)
  | asPtr (dst src : Nat) (writable : Bool)
  | cast (dst src : Nat) (writable : Bool)
  | load (dst mask ptr : Nat)
  | store (dst ptr mask value : Nat)
  | ret

inductive Value where
  | unit
  | view (slice : SliceView) (writable : Bool)
  | ptr (slice : SliceView) (writable signed : Bool)
  | usize (value : Usize)
  | u8 (value : U8)
  | register (value : Word512)

/-- An absent local is dead. A live local may be uninitialized or moved from. -/
abbrev Locals := Nat → Option (Option Value)

structure State where
  locals : Locals
  heap : Memory

def writeLocal (state : State) (slot : Nat) (value : Option (Option Value)) : State :=
  { state with locals := fun index => if index = slot then value else state.locals index }

def init (state : State) (slot : Nat) (value : Value) : Option State :=
  match state.locals slot with
  | some _ => some (writeLocal state slot (some (some value)))
  | none => none

def read (state : State) (slot : Nat) : Option Value := (state.locals slot).join

def move (state : State) (slot : Nat) : Option (Value × State) := do
  let value ← read state slot
  return (value, writeLocal state slot (some none))

def step (permit : Nat → Bool) (state : State) : Op → Option State
  | .live slot =>
    match state.locals slot with
    | none => some (writeLocal state slot (some none))
    | some _ => none
  | .dead slot =>
    match state.locals slot with
    | some _ => some (writeLocal state slot none)
    | none => none
  | .initUnit dst => init state dst .unit
  | .reborrow dst src writable => do
    let .view view sourceMut ← read state src | none
    if writable && !sourceMut then none else init state dst (.view view writable)
  | .copyRegister dst src => do
    let .register value ← read state src | none
    init state dst (.register value)
  | .len dst src => do
    let (.view view false, state) ← move state src | none
    init state dst (.usize view.len)
  | .mask dst src => do
    let (.usize len, state) ← move state src | none
    let .ok mask := (bulksketch.backend.x86_vpclmul512.mask len).match | none
    init state dst (.u8 mask)
  | .asPtr dst src writable => do
    let (.view view sourceMut, state) ← move state src | none
    if writable == sourceMut then init state dst (.ptr view writable false) else none
  | .cast dst src writable => do
    let (.ptr view sourceMut false, state) ← move state src | none
    if writable == sourceMut then init state dst (.ptr view writable true) else none
  | .load dst mask ptr => do
    let (.u8 mask, state) ← move state mask | none
    let (.ptr view false true, state) ← move state ptr | none
    let (value, heap) ← X86MaskedMemory.load state.heap view.base mask.bv
    init {state with heap} dst (.register (unflatten value))
  | .store dst ptr mask value => do
    let (.ptr view true true, state) ← move state ptr | none
    let (.u8 mask, state) ← move state mask | none
    let (.register value, state) ← move state value | none
    let heap ← X86MaskedMemory.store state.heap permit view.base mask.bv (flatten value)
    init {state with heap} dst .unit
  | .ret => none

/-- The terminal instruction reads return slot zero. Mutable caller writeback
is observed by reading the same borrowed address in the returned heap. -/
def exec (permit : Nat → Bool) : List Op → State → Option (Value × Memory)
  | [], _ => none
  | op :: ops, state =>
    match op with
    | .ret => if ops.isEmpty then (read state 0).map fun value => (value, state.heap) else none
    | _ =>
      match step permit state op with
      | some next => exec permit ops next
      | none => none

def loadInput (heap : Memory) (words : SliceView) : State :=
  ⟨fun slot => if slot = 1 then some (some (.view words false)) else none, heap⟩

def storeInput (heap : Memory) (words : SliceView) (value : Word512) : State :=
  ⟨fun slot => if slot = 1 then some (some (.view words true))
    else if slot = 2 then some (some (.register value)) else none, heap⟩

end BulksketchBridge.X86MaskedMemory.Llbc
