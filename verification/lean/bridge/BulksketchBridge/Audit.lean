import BulksketchBridge
import BulksketchBridge.Challenges
import BulksketchBridge.WorkMeterUsedChallenges
import BulksketchBridge.SpreadChallenges
import BulksketchBridge.ReduceChallenges
import BulksketchBridge.Gf64ReduceChallenges
import BulksketchBridge.SquareChallenges
import BulksketchBridge.RawMulTableChallenges
import BulksketchBridge.RawMulAccumChallenges
import BulksketchBridge.RawMulChallenges
import BulksketchBridge.FrobeniusChallenges
import BulksketchBridge.FrobeniusPeriodChallenges
import BulksketchBridge.Algebra.ModulusChallenges
import BulksketchBridge.MapsTraceChallenges
import BulksketchBridge.MapsTraceMathChallenges
import BulksketchBridge.MapsQuadraticChallenges
import BulksketchBridge.MapsCanonicalTraceChallenges
import Lean

open Lean Elab Command Meta

run_cmd do
  let pairs : Array (Name × Name) := #[
    (``BulksketchBridge.Challenges.generatedConstructorMatchesModel,
      ``BulksketchBridge.WorkMeter.new_refines),
    (``BulksketchBridge.Challenges.generatedChargeMatchesExactResultAndState,
      ``BulksketchBridge.WorkMeter.charge_refines),
    (``BulksketchBridge.Challenges.stateProjectionLosesNothing,
      ``BulksketchBridge.WorkMeter.toModel_injective),
    (``BulksketchBridge.Challenges.generatedUsedMatchesExactValue,
      ``BulksketchBridge.WorkMeter.used_refines),
    (``BulksketchBridge.SpreadChallenges.normalResultMatchesModel,
      ``BulksketchBridge.Spread.spread_refines),
    (``BulksketchBridge.SpreadChallenges.allCoefficientsMatch,
      ``BulksketchBridge.Spread.spread_coefficients),
    (``BulksketchBridge.ReduceChallenges.generatedGF64ReductionMatchesModel,
      ``BulksketchBridge.Reduce.reduce64_refines),
    (``BulksketchBridge.ReduceChallenges.generatedGF64ReductionHasDivisionCertificate,
      ``BulksketchBridge.Reduce.reduce64_division_certificate),
    (``BulksketchBridge.Gf64ReduceChallenges.actualGf64ReductionMatchesFoldAndCertificate,
      ``BulksketchBridge.Gf64Reduce.reduce_refines),
    (``BulksketchBridge.SquareChallenges.normalResultMatchesModel,
      ``BulksketchBridge.Square.square_refines),
    (``BulksketchBridge.SquareChallenges.rawSquareDivisionCertificate,
      ``BulksketchBridge.Square.square_division_certificate),
    (``BulksketchBridge.RawMulTableChallenges.initializedTableLoopCompletes,
      ``BulksketchBridge.RawMulTable.initialized_table_loop_completes),
    (``BulksketchBridge.RawMulTableChallenges.everyInitializedPrefixCompletes,
      ``BulksketchBridge.RawMulTable.every_initialized_prefix_completes),
    (``BulksketchBridge.RawMulAccumChallenges.nibbleShiftsIndicesAndCastsAreSafe,
      ``BulksketchBridge.RawMulAccum.nibble_bounds),
    (``BulksketchBridge.RawMulAccumChallenges.eachOriginalBodyPreservesPrefix,
      ``BulksketchBridge.RawMulAccum.body_step),
    (``BulksketchBridge.RawMulAccumChallenges.originalBodyStopsBeforeShift64,
      ``BulksketchBridge.RawMulAccum.terminal_body),
    (``BulksketchBridge.RawMulAccumChallenges.everyOriginalPrefixCompletes,
      ``BulksketchBridge.RawMulAccum.every_prefix_completes),
    (``BulksketchBridge.RawMulChallenges.actualRawMultiplicationReturnsEveryBit,
      ``BulksketchBridge.RawMul.raw_mul_refines),
    (``BulksketchBridge.RawMulChallenges.actualRawMultiplicationHasConvolutionCoefficients,
      ``BulksketchBridge.RawMul.raw_mul_coefficients),
    (``BulksketchBridge.RawMulChallenges.actualMultiplicationHasDivisionCertificate,
      ``BulksketchBridge.RawMul.mul_division_certificate),
    (``BulksketchBridge.FrobeniusChallenges.normalResultMatchesIteratedSquare,
      ``BulksketchBridge.Frobenius.frobenius_refines),
    (``BulksketchBridge.FrobeniusPeriodChallenges.oldFrozenModelMatchesCoreExactly,
      ``BulksketchBridge.FrobeniusPeriod.model_correspondence),
    (``BulksketchBridge.FrobeniusPeriodChallenges.oldFrozenModelHasPeriod64,
      ``BulksketchBridge.FrobeniusPeriod.existing_period64),
    (``BulksketchBridge.FrobeniusPeriodChallenges.oldFrozenModelIterationCountsReduceModulo64,
      ``BulksketchBridge.FrobeniusPeriod.existing_iteration_mod64),
    (``BulksketchBridge.FrobeniusPeriodChallenges.actualNativeFrobeniusMatchesUnmoddedIteration,
      ``BulksketchBridge.FrobeniusPeriod.native_unmodded_refines),
    (``BulksketchBridge.Algebra.ModulusChallenges.exactPolynomialIrreducible,
      ``BulksketchBridge.Algebra.Gf64.exactPolynomialIrreducible),
    (``BulksketchBridge.MapsTraceChallenges.normalResultMatchesSelector,
      ``BulksketchBridge.MapsTrace.trace_refines),
    (``BulksketchBridge.MapsTraceMathChallenges.actualTraceMatchesAbsoluteTrace,
      ``BulksketchBridge.MapsTraceMath.trace_matches_absolute),
    (``BulksketchBridge.MapsQuadraticChallenges.allGeneratedRowsMatchSourceData,
      ``BulksketchBridge.MapsTables.rows_match_source),
    (``BulksketchBridge.MapsQuadraticChallenges.allGeneratedChunksMatchSourceData,
      ``BulksketchBridge.MapsTables.chunks_match_source),
    (``BulksketchBridge.MapsQuadraticChallenges.actualRowsReturnExactSourceData,
      ``BulksketchBridge.MapsTables.quadratic_rows_refines),
    (``BulksketchBridge.MapsQuadraticChallenges.actualValueMatchesAllChunkContributions,
      ``BulksketchBridge.MapsQuadratic.quadratic_value_refines),
    (``BulksketchBridge.MapsQuadraticChallenges.actualValueMatchesIndependentMatrix,
      ``BulksketchBridge.MapsQuadratic.quadratic_value_matches_matrix),
    (``BulksketchBridge.MapsQuadraticChallenges.actualSolverMatchesNormalizedModel,
      ``BulksketchBridge.MapsQuadratic.solve_quadratic_refines),
    (``BulksketchBridge.MapsQuadraticChallenges.actualSolverHasExactNormalizedSolutionMeaning,
      ``BulksketchBridge.MapsQuadratic.solve_quadratic_exact_meaning),
    (``BulksketchBridge.MapsCanonicalTraceChallenges.normalResultMatchesAbsoluteTrace,
      ``BulksketchBridge.MapsCanonicalTrace.canonical_trace_refines)
  ]
  for (challenge, solution) in pairs do
    let expected ← getConstInfo challenge
    let actual ← getConstInfo solution
    let .defnInfo expected := expected | throwError "challenge must be a proposition definition"
    let .thmInfo actual := actual | throwError "challenge solution must be a theorem"
    unless ← liftTermElabM <| isDefEq actual.type expected.value do
      throwError "bridge challenge statement mismatch: {solution}"
    let proposition ← liftTermElabM <| whnf expected.value
    logInfo <| Json.compress <| Json.mkObj [
      ("kind", toJson "challenge_match"), ("challenge", toJson challenge.toString),
      ("theorem", toJson solution.toString),
      ("referenced_constants", toJson <| proposition.getUsedConstants.map Name.toString)]
  let environment ← getEnv
  let runtimeProofs := #[
    ``Aeneas.Std.trailingZeroCount_le_width,
    ``Aeneas.Std.usize_trailing_zeros_spec,
    ``Aeneas.Std.usize_trailing_zeros_zero,
    ``Aeneas.Std.usize_trailing_zeros_least_set_bit,
    ``Aeneas.Std.trailingZeroCount_eq_of_toNat_eq,
    ``Aeneas.Std.usize_trailing_zeros_nibble,
    ``Aeneas.Std.checked_unsigned_conversion_normal,
    ``Aeneas.Std.u64_count_ones_spec,
    ``Aeneas.Std.result_expect_independent_of_debug]
  let names := environment.constants.toList.filterMap fun (declarationName, information) =>
    match information with
    | .thmInfo _ =>
        if declarationName.toString.startsWith "BulksketchBridge." || runtimeProofs.contains declarationName
        then some declarationName else none
    | _ => none
  let names := names.toArray.qsort Name.lt
  let permitted := #[``propext, ``Quot.sound, ``Classical.choice]
  for declarationName in runtimeProofs do
    unless names.contains declarationName do throwError "runtime model theorem missing from audit"
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
