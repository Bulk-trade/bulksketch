import Lean.CoreM
import Lean.Replay
import LeanExport.Parse

/-!
Replay an exported core string prelude before an exported proof environment.

Lean 4.35's replay dependency collector does not schedule the implicit
String.ofList dependency of a string literal. This driver changes only loading
order: both phases use the original parser and Kernel.Environment.replay. It
does not change declarations, kernel rules, or the original main export.

The prelude and main export must contain only safe, non-partial declarations
and the three permitted standard axioms. A main declaration may be omitted
only when structurally identical to the original prelude declaration submitted
for checking. Kernel-generated recursors may rename binders; checked objects
also must match the submitted objects using upstream ConstantInfo equality.
Quotient declarations receive the upstream checkExport checks.
-/

open Lean

namespace BulksketchVerification.ReplayExport

abbrev ConstantMap := Std.HashMap Name ConstantInfo

private def quotientConstructors : List Name := [`Quot.mk, `Quot.lift, `Quot.ind]

private def permittedAxioms : List Name := [`propext, `Quot.sound, `Classical.choice]

private def parseExport (path : String) : IO LeanExport.ExportedEnv :=
  IO.FS.withFile path .read fun handle =>
    LeanExport.parseStream (.ofHandle handle)

private def checkInput (label : String) (constants : ConstantMap) : IO Unit := do
  for (name, info) in constants.toList do
    if info.isUnsafe || info.isPartial then
      throw <| IO.userError s!"{label}: unsafe or partial declaration '{name}' cannot be replayed"
    if let .axiomInfo axiomInfo := info then
      unless permittedAxioms.contains axiomInfo.name do
        throw <| IO.userError s!"{label}: unpermitted axiom '{axiomInfo.name}'"

private def checkQuotients (label : String) (constants : ConstantMap)
    (environment : Kernel.Environment) : IO Unit := do
  for name in `Quot :: quotientConstructors do
    if let some original := constants[name]? then
      let some checked := environment.find? name |
        throw <| IO.userError s!"{label}: quotient constant missing after replay: '{name}'"
      unless original == checked do
        throw <| IO.userError s!"{label}: quotient constant mismatch: '{name}'"

private def sameConstant (left right : ConstantInfo) : Bool :=
  -- ConstantInfo's derived BEq uses alpha-equivalence for expressions. Check
  -- their structure too, including binder names/annotations and rule bodies.
  left == right && left.type.equal right.type &&
    (match left.value? (allowOpaque := true), right.value? (allowOpaque := true) with
      | none, none => true
      | some left, some right => left.equal right
      | _, _ => false) &&
    (match left, right with
      | .recInfo left, .recInfo right =>
        (left.rules.zip right.rules).all fun (left, right) => left.rhs.equal right.rhs
      | _, _ => true)

private def replayPhase (label : String) (constants : ConstantMap)
    (environment : Kernel.Environment) : IO Kernel.Environment := do
  -- Adding Quot causes the kernel to generate these three constants itself.
  -- Their exact exported definitions are checked immediately after replay,
  -- as in the pinned upstream LeanChecker.checkExport implementation.
  let replayConstants := quotientConstructors.foldl (init := constants) (·.erase ·)
  let checked ← environment.replay replayConstants
  checkQuotients label constants checked
  return checked

def run (arguments : List String) : IO UInt32 := do
  try
    let [preludePath, mainPath] := arguments |
      throw <| IO.userError "usage: lean --run ReplayExport.lean CORE_PRELUDE_EXPORT MAIN_EXPORT"
    let prelude ← parseExport preludePath
    let main ← parseExport mainPath
    checkInput "prelude" prelude.constMap
    checkInput "main" main.constMap
    -- This is an ordering-only prelude, never an extension of the main export.
    for (name, submitted) in prelude.constMap.toList do
      let some original := main.constMap[name]? |
        throw <| IO.userError s!"prelude: declaration absent from main export: '{name}'"
      unless sameConstant original submitted do
        throw <| IO.userError s!"main: conflicting preloaded declaration '{name}'"
    for name in [`String.ofList, `Char.ofNat] do
      unless prelude.constMap.contains name do
        throw <| IO.userError s!"prelude: '{name}' declaration is required"
    let empty ← Lean.mkEmptyEnvironment
    let preloaded ← replayPhase "prelude" prelude.constMap empty.toKernelEnv
    for name in [`String.ofList, `Char.ofNat] do
      unless (preloaded.find? name).isSome do
        throw <| IO.userError s!"prelude: '{name}' was not kernel checked"
    let mut remaining := main.constMap
    let mut duplicateCount := 0
    for (name, original) in main.constMap.toList do
      if let some checked := preloaded.find? name then
        if let some submitted := prelude.constMap[name]? then
          unless sameConstant original submitted do
            throw <| IO.userError s!"main: conflicting preloaded declaration '{name}'"
          unless submitted == checked do
            throw <| IO.userError s!"prelude: checked declaration mismatch '{name}'"
          remaining := remaining.erase name
          duplicateCount := duplicateCount + 1
    let checked ← replayPhase "main" remaining preloaded
    checkQuotients "main" main.constMap checked
    IO.println s!"Lean default kernel accepts prelude ({prelude.constMap.size} declarations) and main ({remaining.size} replayed, {duplicateCount} identical preloaded declarations)"
    return 0
  catch error =>
    IO.eprintln s!"Export replay rejected: {error}"
    return 1

end BulksketchVerification.ReplayExport

def main (arguments : List String) : IO UInt32 :=
  BulksketchVerification.ReplayExport.run arguments
