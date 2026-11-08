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
import BulksketchBridge.Algebra.WordChallenges
import BulksketchBridge.Algebra.WordNativeChallenges
import BulksketchBridge.Algebra.TraceChallenges
import BulksketchBridge.Algebra.TraceNativeChallenges
import BulksketchBridge.Algebra.InversePowerChallenges
import BulksketchBridge.InverseChallenges
import BulksketchBridge.PortableChallenges
import BulksketchBridge.InverseUsingChallenges
import BulksketchBridge.PortableInverseChallenges
import BulksketchBridge.FrobeniusConstChallenges
import BulksketchBridge.FrobeniusLookupChallenges
import BulksketchBridge.SliceKernelChallenges
import BulksketchBridge.PortableSliceChallenges
import BulksketchBridge.PortableXorChallenges
import BulksketchBridge.DenseNormalizationSpec
import BulksketchBridge.DenseCoefficientSpec
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
      ``BulksketchBridge.MapsCanonicalTrace.canonical_trace_refines),
    (``BulksketchBridge.Algebra.Gf64.WordChallenges.ExactPolynomialCoefficients,
      ``BulksketchBridge.Algebra.Gf64.exact_polynomial_coefficients),
    (``BulksketchBridge.Algebra.Gf64.WordChallenges.BijectiveRepresentation,
      ``BulksketchBridge.Algebra.Gf64.bijective_representation),
    (``BulksketchBridge.Algebra.Gf64.WordChallenges.AdditiveRepresentation,
      ``BulksketchBridge.Algebra.Gf64.additive_representation),
    (``BulksketchBridge.Algebra.Gf64.WordChallenges.CompleteRawProduct,
      ``BulksketchBridge.Algebra.Gf64.complete_raw_product),
    (``BulksketchBridge.Algebra.Gf64.WordChallenges.ReductionRepresentation,
      ``BulksketchBridge.Algebra.Gf64.reduction_representation),
    (``BulksketchBridge.Algebra.Gf64.WordChallenges.MultiplicationRepresentation,
      ``BulksketchBridge.Algebra.Gf64.multiplication_representation),
    (``BulksketchBridge.Algebra.Gf64.WordChallenges.SquareRepresentation,
      ``BulksketchBridge.Algebra.Gf64.square_representation),
    (``BulksketchBridge.Algebra.Gf64.WordChallenges.ArithmeticFieldLaws,
      ``BulksketchBridge.Algebra.Gf64.arithmetic_field_laws),
    (``BulksketchBridge.Algebra.Gf64.WordNativeChallenges.actualReductionIsQuotientRemainder,
      ``BulksketchBridge.Algebra.Gf64.native_reduce_is_quotient),
    (``BulksketchBridge.Algebra.Gf64.WordNativeChallenges.actualMultiplicationIsFieldMultiplication,
      ``BulksketchBridge.Algebra.Gf64.native_mul_is_field),
    (``BulksketchBridge.Algebra.Gf64.WordNativeChallenges.actualSquareIsFieldSquare,
      ``BulksketchBridge.Algebra.Gf64.native_square_is_field),
    (``BulksketchBridge.Algebra.Gf64.WordNativeChallenges.actualFrobeniusIsFieldPower,
      ``BulksketchBridge.Algebra.Gf64.native_frobenius_is_field),
    (``BulksketchBridge.Algebra.Gf64.TraceChallenges.wordAbsoluteTraceIsAlgebraTrace,
      ``BulksketchBridge.Algebra.Gf64.word_absolute_trace_transport),
    (``BulksketchBridge.Algebra.Gf64.TraceChallenges.nativeSelectorIsAlgebraTrace,
      ``BulksketchBridge.Algebra.Gf64.native_selector_trace_transport),
    (``BulksketchBridge.Algebra.Gf64.TraceNativeChallenges.actualTraceIsAlgebraTrace,
      ``BulksketchBridge.Algebra.Gf64.native_trace_is_algebra_trace),
    (``BulksketchBridge.Algebra.Gf64.TraceNativeChallenges.actualCanonicalTraceIsAlgebraTrace,
      ``BulksketchBridge.Algebra.Gf64.native_canonical_trace_is_algebra_trace),
    (``BulksketchBridge.Algebra.Gf64.InversePowerChallenges.fieldPowerPeriod,
      ``BulksketchBridge.Algebra.Gf64.field_power_period),
    (``BulksketchBridge.Algebra.Gf64.InversePowerChallenges.fieldInverseExponent,
      ``BulksketchBridge.Algebra.Gf64.field_inverse_power),
    (``BulksketchBridge.InverseChallenges.actualSourceReturnsExactChain,
      ``BulksketchBridge.Inverse.exact_chain_refines),
    (``BulksketchBridge.InverseChallenges.actualSourceReturnsFieldInverse,
      ``BulksketchBridge.Inverse.field_inverse_refines),
    (``BulksketchBridge.InverseChallenges.nativeCallbackInstanceReturnsFieldInverse,
      ``BulksketchBridge.Inverse.native_callback_instance),
    (``BulksketchBridge.PortableChallenges.actualMultiplicationIsFieldMultiplication,
      ``BulksketchBridge.Portable.mul_refines),
    (``BulksketchBridge.PortableChallenges.actualSquareIsFieldSquare,
      ``BulksketchBridge.Portable.square_refines),
    (``BulksketchBridge.PortableChallenges.actualFrobeniusIsFullFieldPower,
      ``BulksketchBridge.Portable.frobenius_refines),
    (``BulksketchBridge.PortableChallenges.actualTraceIsAlgebraTrace,
      ``BulksketchBridge.Portable.trace_refines),
    (``BulksketchBridge.PortableChallenges.actualQuadraticHasNormalizedFieldMeaning,
      ``BulksketchBridge.Portable.solve_quadratic_refines),
    (``BulksketchBridge.PortableChallenges.actualRawMultiplicationReturnsFullProduct,
      ``BulksketchBridge.Portable.raw_mul_refines),
    (``BulksketchBridge.PortableChallenges.actualReductionIsExactQuotientRemainder,
      ``BulksketchBridge.Portable.reduce_refines),
    (``BulksketchBridge.InverseUsingChallenges.capturedSquareReturnsEveryIteration,
      ``BulksketchBridge.InverseUsing.captured_square_refines),
    (``BulksketchBridge.InverseUsingChallenges.actualInverseUsingReturnsFieldInverse,
      ``BulksketchBridge.InverseUsing.inverse_using_refines),
    (``BulksketchBridge.InverseUsingChallenges.actualInverseReturnsFieldInverse,
      ``BulksketchBridge.InverseUsing.inverse_refines),
    (``BulksketchBridge.PortableInverseChallenges.actualInverseReturnsFieldInverse,
      ``BulksketchBridge.PortableInverse.inverse_refines),
    (``BulksketchBridge.FrobeniusConstChallenges.actualConstSquareMatchesWord,
      ``BulksketchBridge.FrobeniusConst.square_refines),
    (``BulksketchBridge.FrobeniusTable.TablesRefine,
      ``BulksketchBridge.FrobeniusTables.tables_refines),
    (``BulksketchBridge.FrobeniusTable.InverseTableRefines,
      ``BulksketchBridge.FrobeniusInverseTable.inverse21_table_refines),
    (``BulksketchBridge.FrobeniusTable.LookupRefines,
      ``BulksketchBridge.FrobeniusTable.lookup_refines),
    (``BulksketchBridge.FrobeniusTable.InverseLookupRefines,
      ``BulksketchBridge.FrobeniusTable.inverse21_refines),
    (``BulksketchBridge.SliceKernelChallenges.actualMultiplyLinearReturnsExactFrame,
      ``BulksketchBridge.SliceKernels.multiply_linear_refines),
    (``BulksketchBridge.SliceKernelChallenges.actualSquareModFallbackPreservesBuffers,
      ``BulksketchBridge.SliceKernels.square_mod_fallback_refines),
    (``BulksketchBridge.FrobeniusTable.StaticTablesRefine,
      ``BulksketchBridge.FrobeniusTable.static_tables_refine),
    (``BulksketchBridge.FrobeniusTable.StaticInverseTableRefines,
      ``BulksketchBridge.FrobeniusTable.static_inverse_table_refines),
    (``BulksketchBridge.SliceKernels.PaddedProductRefines,
      ``BulksketchBridge.SliceKernels.multiply_linear_padded_product),
    (``BulksketchBridge.PortableXorChallenges.actualXorAssignReturnsFrame,
      ``BulksketchBridge.PortableXor.xor_assign_refines),
    (``BulksketchBridge.PortableSliceChallenges.squareRefines,
      ``BulksketchBridge.PortableSlice.square_slice_refines),
    (``BulksketchBridge.PortableSliceChallenges.scaleRefines,
      ``BulksketchBridge.PortableSlice.scale_xor_refines),
    (``BulksketchBridge.DenseNormalization.NormalizedLenRefines,
      ``BulksketchBridge.DenseNormalization.normalized_len_refines),
    (``BulksketchBridge.DenseCoefficient.XorCoefficientRefines,
      ``BulksketchBridge.DenseCoefficient.xor_coefficient_refines),
    (``BulksketchBridge.DenseCoefficient.XorCoefficientPolynomialRefines,
      ``BulksketchBridge.DenseCoefficient.xor_coefficient_polynomial_refines),
    (``BulksketchBridge.VerifyDispatch.ProductCountsRefines,
      ``BulksketchBridge.VerifyDispatch.product_counts_refines),
    (``BulksketchBridge.VerifyDispatch.UseRebuiltLfsrRefines,
      ``BulksketchBridge.VerifyDispatch.use_rebuilt_lfsr_refines),
    (``BulksketchBridge.ShapeWireChallenges.actualRecordBytesMatchesWireBounds,
      ``BulksketchBridge.ShapeWire.record_bytes_refines),
    (``BulksketchBridge.Reconciliation.GF64OddSyndromesDeterminePositivePowers,
      ``BulksketchBridge.Reconciliation.gf64_positive_powerSums),
    (``BulksketchBridge.Reconciliation.GF64OddSyndromesIdentifySparseSupport,
      ``BulksketchBridge.Reconciliation.gf64_sparse_support_unique),
    (``BulksketchBridge.Reconciliation.GF64RebuiltLocatorRecurrence,
      ``BulksketchBridge.Reconciliation.gf64_rebuilt_locator_recurrence),
    (``BulksketchBridge.Reconciliation.GF64RebuiltVerificationIffDirect,
      ``BulksketchBridge.Reconciliation.gf64_rebuilt_verification_iff_direct),
    (``BulksketchBridge.Reconciliation.GF64PositiveLocatorMinimal,
      ``BulksketchBridge.Reconciliation.gf64_positive_locator_minimal),
    (``BulksketchBridge.Reconciliation.GF64PositiveLocatorUnique,
      ``BulksketchBridge.Reconciliation.gf64_positive_locator_unique),
    (``BulksketchBridge.OddRecurrence.ActualDefaultMatchesEveryContinuation,
      ``BulksketchBridge.OddRecurrence.default_refines),
    (``BulksketchBridge.Reconciliation.GF64ScalarContinuationIffDirect,
      ``BulksketchBridge.Reconciliation.gf64_scalar_continuation_iff_direct),
    (``BulksketchBridge.DenseSquareChallenges.actualSquareIntoReturnsExactFrame,
      ``BulksketchBridge.DenseSquare.square_into_refines),
    (``BulksketchBridge.DenseSquare.SquareIntoPolynomialRefines,
      ``BulksketchBridge.DenseSquare.square_into_polynomial_refines),
    (``BulksketchBridge.PortableEncodingChallenges.actualInsertNonzeroReturnsFrame,
      ``BulksketchBridge.PortableEncoding.insert_nonzero_refines),
    (``BulksketchBridge.PortableEncodingChallenges.actualEncodeNonzeroReturnsFrame,
      ``BulksketchBridge.PortableEncoding.encode_nonzero_refines),
    (``BulksketchBridge.AffineLinearEval.ActualLinearEvaluation,
      ``BulksketchBridge.AffineLinearEval.linear_eval_refines),
    (``BulksketchBridge.RebuiltLfsr.ActualRebuiltLfsrReturnsFrames,
      ``BulksketchBridge.RebuiltLfsr.rebuilt_lfsr_refines),
    (``BulksketchBridge.RebuiltLfsr.ActualRebuiltLfsrIffDirect,
      ``BulksketchBridge.RebuiltLfsr.rebuilt_lfsr_iff_direct),
    (``BulksketchBridge.DenseMulReductionSpec.finalReductionFrame,
      ``BulksketchBridge.DenseMulReduction.loop_refines),
    (``BulksketchBridge.RebuiltLfsr.ActualRebuiltLfsrWithPortableSeed,
      ``BulksketchBridge.RebuiltLfsr.rebuilt_lfsr_portable_seed_refines),
    (``BulksketchBridge.DenseMul.ActualDenseMulReturnsExactFrames,
      ``BulksketchBridge.DenseMul.mul_into_refines),
    (``BulksketchBridge.DenseMulConvolutionSpec.innerLoopFrame,
      ``BulksketchBridge.DenseMulConvolution.inner_loop_refines),
    (``BulksketchBridge.DenseMulConvolutionSpec.outerLoopFrame,
      ``BulksketchBridge.DenseMulConvolution.outer_loop_refines),
    (``BulksketchBridge.DenseMul.ActualDenseMulPolynomialProduct,
      ``BulksketchBridge.DenseMul.mul_into_polynomial_refines),
    (``BulksketchBridge.DirectTwo.ActualDirectTwoReturnsNormalizedPair,
      ``BulksketchBridge.DirectTwo.direct_two_refines),
    (``BulksketchBridge.DirectTwo.ActualDirectTwoSound,
      ``BulksketchBridge.DirectTwo.direct_two_sound),
    (``BulksketchBridge.PortableHornerChallenges.hornerRefines,
      ``BulksketchBridge.PortableHorner.horner_many_refines),
    (``BulksketchBridge.PortableHorner.ActualPortableHornerEvaluatesPolynomial,
      ``BulksketchBridge.PortableHorner.horner_many_polynomial_refines),
    (``BulksketchBridge.X86LaneMask.ActualMaskReturnsLowLanes,
      ``BulksketchBridge.X86LaneMask.mask_refines),
    (``BulksketchBridge.X86Pclmul.WordRefines,
      ``BulksketchBridge.X86Pclmul.word_refines),
    (``BulksketchBridge.X86Pclmul.LowRefines,
      ``BulksketchBridge.X86Pclmul.low_refines),
    (``BulksketchBridge.X86Pclmul.WordsRefines,
      ``BulksketchBridge.X86Pclmul.words_refines),
    (``BulksketchBridge.X86Pclmul.RawProductRefines,
      ``BulksketchBridge.X86Pclmul.raw_product_refines),
    (``BulksketchBridge.X86Pclmul.ReducedRefines,
      ``BulksketchBridge.X86Pclmul.reduced_refines),
    (``BulksketchBridge.X86Pclmul.MultiplyRefines,
      ``BulksketchBridge.X86Pclmul.multiply_refines),
    (``BulksketchBridge.X86Pclmul.MulRefines,
      ``BulksketchBridge.X86Pclmul.mul_refines),
    (``BulksketchBridge.X86Pclmul.SquareRefines,
      ``BulksketchBridge.X86Pclmul.square_refines),
    (``BulksketchBridge.X86Pclmul.RawMulRefines,
      ``BulksketchBridge.X86Pclmul.raw_mul_refines),
    (``BulksketchBridge.Avx512RegisterChallenges.rawRefines,
      ``BulksketchBridge.Avx512Register.raw_refines),
    (``BulksketchBridge.Avx512RegisterChallenges.reduceShiftRefines,
      ``BulksketchBridge.Avx512Register.reduce_shift_refines),
    (``BulksketchBridge.Avx512RegisterChallenges.reduceClRefines,
      ``BulksketchBridge.Avx512Register.reduce_cl_refines),
    (``BulksketchBridge.Avx512RegisterChallenges.multiplyRefines,
      ``BulksketchBridge.Avx512Register.multiply_refines),
    (``BulksketchBridge.CubeRoot.ActualCubeRootComplete,
      ``BulksketchBridge.CubeRoot.cube_root_refines),
    (``BulksketchBridge.X86MaskedMemory.PureExtraction.PureStoreWritebackImpossible,
      ``BulksketchBridge.X86MaskedMemory.PureExtraction.pure_store_cannot_writeback),
    (``BulksketchBridge.X86MaskedMemory.PureExtraction.PureLoadTwoWordsImpossible,
      ``BulksketchBridge.X86MaskedMemory.PureExtraction.pure_load_cannot_read_two_words),
    (``BulksketchBridge.X86MaskedMemory.StatefulRegisterPayload,
      ``BulksketchBridge.X86MaskedMemory.store_register_payload)
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
