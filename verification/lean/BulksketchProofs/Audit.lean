import BulksketchProofs
import BulksketchProofs.Challenges
import BulksketchProofs.SpreadChallenges
import Lean

open Lean Elab Command Meta

/-! Check exact challenge types and every public project theorem's axiom closure.
These commands do not manufacture proof terms or alter the kernel environment. -/

run_cmd do
  let pairs : Array (Name × Name) := #[
    (``BulksketchProofs.Challenges.reductionCertificate,
      ``BulksketchProofs.Field.generated_reduction_division_certificate),
    (``BulksketchProofs.Challenges.generatedExpressionMatchesModel,
      ``BulksketchProofs.Field.generated_reduce_eq_model),
    (``BulksketchProofs.Challenges.remainderHasCanonicalDegree,
      ``BulksketchProofs.Field.generated_remainder_high_bits),
    (``BulksketchProofs.Challenges.reductionCertificateIsUnique,
      ``BulksketchProofs.Field.generated_reduction_certificate_unique),
    (``BulksketchProofs.Challenges.reductionIsXorLinear,
      ``BulksketchProofs.Field.generated_reduction_xor),
    (``BulksketchProofs.Challenges.spreadPreservesExactlyTheEvenCoefficients,
      ``BulksketchProofs.Field.spread64_bits),
    (``BulksketchProofs.Challenges.rawSquareDoublesExactlyTheCoefficientIndices,
      ``BulksketchProofs.Field.rawSquare128_bits),
    (``BulksketchProofs.Challenges.chargeSucceedsExactly,
      ``BulksketchProofs.Resource.WorkMeter.charge_success_iff),
    (``BulksketchProofs.Challenges.deniedChargePreservesUsed,
      ``BulksketchProofs.Resource.WorkMeter.used_unchanged_on_failure),
    (``BulksketchProofs.Challenges.boundedAccountingIsPreserved,
      ``BulksketchProofs.Resource.WorkMeter.bounded_preserved),
    (``BulksketchProofs.Challenges.successfulSequenceAccountsExactly,
      ``BulksketchProofs.Resource.WorkMeter.successful_charges_sum),
    (``BulksketchProofs.Challenges.exhaustedMeterRejectsEveryCharge,
      ``BulksketchProofs.Resource.WorkMeter.exhausted_sticky)
  ]
  for (challenge, solution) in pairs do
    let expected ← getConstInfo challenge
    let actual ← getConstInfo solution
    let .defnInfo expected := expected | throwError "challenge must be a proposition definition"
    let .thmInfo actual := actual | throwError "challenge solution must be a theorem: {solution}"
    unless ← liftTermElabM <| isDefEq actual.type expected.value do
      throwError "frozen statement mismatch: {solution}"
    logInfo <| Json.compress <| Json.mkObj [
      ("kind", toJson "challenge_match"), ("challenge", toJson challenge.toString),
      ("theorem", toJson solution.toString)]
  let environment ← getEnv
  let names := environment.constants.toList.filterMap fun (name, information) =>
    match information with
    | .thmInfo _ => if name.toString.startsWith "BulksketchProofs." then some name else none
    | _ => none
  let names := names.toArray.qsort Name.lt
  for (_, solution) in pairs do
    unless names.contains solution do
      throwError "frozen challenge solution missing from audited theorem roots: {solution}"
  let permitted := #[``propext, ``Quot.sound, ``Classical.choice]
  for name in names do
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless permitted.contains axiomName do
        throwError "forbidden axiom {axiomName} in {name}"
    logInfo <| Json.compress <| Json.mkObj [
      ("kind", toJson "theorem_axioms"), ("theorem", toJson name.toString),
      ("axioms", toJson <| axioms.map Name.toString)]
  logInfo <| Json.compress <| Json.mkObj [
    ("kind", toJson "summary"), ("public_theorems", toJson names.size),
    ("matched_challenges", toJson pairs.size)]
