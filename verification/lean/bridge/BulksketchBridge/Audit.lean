import BulksketchBridge
import BulksketchBridge.Challenges
import Lean

open Lean Elab Command Meta

run_cmd do
  let pairs : Array (Name × Name) := #[
    (``BulksketchBridge.Challenges.generatedConstructorMatchesModel,
      ``BulksketchBridge.WorkMeter.new_refines),
    (``BulksketchBridge.Challenges.generatedChargeMatchesExactResultAndState,
      ``BulksketchBridge.WorkMeter.charge_refines),
    (``BulksketchBridge.Challenges.stateProjectionLosesNothing,
      ``BulksketchBridge.WorkMeter.toModel_injective)
  ]
  for (challenge, solution) in pairs do
    let expected ← getConstInfo challenge
    let actual ← getConstInfo solution
    let .defnInfo expected := expected | throwError "challenge must be a proposition definition"
    let .thmInfo actual := actual | throwError "challenge solution must be a theorem"
    unless ← liftTermElabM <| isDefEq actual.type expected.value do
      throwError "bridge challenge statement mismatch: {solution}"
    logInfo <| Json.compress <| Json.mkObj [
      ("kind", toJson "challenge_match"), ("challenge", toJson challenge.toString),
      ("theorem", toJson solution.toString)]
  let environment ← getEnv
  let names := environment.constants.toList.filterMap fun (declarationName, information) =>
    match information with
    | .thmInfo _ => if declarationName.toString.startsWith "BulksketchBridge." then some declarationName else none
    | _ => none
  let names := names.toArray.qsort Name.lt
  let permitted := #[``propext, ``Quot.sound, ``Classical.choice]
  for (_, solution) in pairs do
    unless names.contains solution do throwError "bridge root missing from theorem audit"
  for declarationName in names do
    let axioms ← collectAxioms declarationName
    for axiomName in axioms do
      unless permitted.contains axiomName do throwError "forbidden bridge axiom {axiomName}"
    logInfo <| Json.compress <| Json.mkObj [
      ("kind", toJson "theorem_axioms"), ("theorem", toJson declarationName.toString),
      ("axioms", toJson <| axioms.map Name.toString)]
  logInfo <| Json.compress <| Json.mkObj [
    ("kind", toJson "summary"), ("public_theorems", toJson names.size),
    ("matched_challenges", toJson pairs.size)]
