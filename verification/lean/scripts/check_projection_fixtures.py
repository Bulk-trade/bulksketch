#!/usr/bin/env python3
"""Reject edits to original generated bodies and shared extraction boundaries."""
from pathlib import Path
import importlib.util
import json
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PROJECTIONS = [
    ("inverse", "extraction/inverse-chain/project.py", "extraction/inverse-chain/receipt.json",
     "extraction/inverse-chain/Inverse/Funs.lean", "bridge/Arithmetic/InverseGenerated.lean",
     "if a = 0#u64", "if a = 1#u64", "compiled inverse projection differs", "shared type mismatch", "shared dictionary/function mismatch", []),
    ("portable", "extraction/portable-forwarding/project.py", "extraction/portable-forwarding/receipt.json",
     "extraction/portable-forwarding/Portable/Funs.lean", "bridge/Arithmetic/PortableGenerated.lean",
     "field.gf64.mul fieldBinaryFieldInst a b", "field.gf64.mul fieldBinaryFieldInst a a",
     "compiled Portable projection differs", "shared type mismatch", "shared function/dictionary mismatch", []),
    ("portable-inverse", "extraction/portable-inverse/project.py", "extraction/portable-inverse/receipt.json",
     "extraction/portable-inverse/PortableInverse/Funs.lean", "bridge/Arithmetic/PortableInverseGenerated.lean",
     "field.maps.inverse fieldBinaryFieldInst a", "field.maps.inverse fieldBinaryFieldInst 0#u64",
     "compiled Portable projection differs", "shared type mismatch", "shared function/dictionary mismatch",
     ["bridge/Arithmetic/InverseGenerated.lean", "bridge/Arithmetic/InverseUsingTypes.lean",
      "bridge/Arithmetic/InverseUsingGenerated.lean"]),
    ("wrappers", "extraction/inverse-wrappers/project.py", "extraction/inverse-wrappers/receipt.json",
     "extraction/inverse-wrappers/Arithmetic/Funs.lean", "bridge/Arithmetic/InverseUsingGenerated.lean",
     "coreopsfunctionFnT2TupleU64U64Inst.call c value", "coreopsfunctionFnT2TupleU64U64Inst.call c 0#u64",
     "compiled wrapper projection differs", "shared wrapper type mismatch", "shared wrapper function/dictionary mismatch",
     ["bridge/Arithmetic/InverseUsingTypes.lean", "bridge/Arithmetic/InverseGenerated.lean"]),
    ("frobenius", "extraction/frobenius-const/project.py", "extraction/frobenius-const/square/receipt.json",
     "extraction/frobenius-const/square/Arithmetic/Funs.lean", "bridge/Arithmetic/FrobeniusConstGenerated.lean",
     "if bit < 64#i32", "if bit < 63#i32", "compiled const-square projection differs", None, None, []),
    ("frobenius-tables", "extraction/frobenius-const/tables-lookup/project.py",
     "extraction/frobenius-const/tables-lookup/receipt.json",
     "extraction/frobenius-const/tables-lookup/Arithmetic/Funs.lean",
     "bridge/Arithmetic/FrobeniusTablesGenerated.lean",
     "if value < 16#usize", "if value < 15#usize", "compiled Frobenius projection differs",
     None, None, ["bridge/Arithmetic/FrobeniusConstGenerated.lean"]),
    ("slice-kernels", "extraction/slice-kernels/project.py",
     "extraction/slice-kernels/multiply-linear/receipt.json",
     "extraction/slice-kernels/multiply-linear/Arithmetic/Funs.lean",
     "bridge/Arithmetic/SliceKernelGenerated.lean",
     "ok (false, _dst, _raw)", "ok (true, _dst, _raw)", "compiled slice body projection differs",
     None, None, ["bridge/Arithmetic/SliceKernelTypes.lean"]),
    ("portable-xor", "extraction/portable-xor/project.py", "extraction/portable-xor/receipt.json",
     "extraction/portable-xor/Arithmetic/Funs.lean", "bridge/Arithmetic/PortableXorGenerated.lean",
     "lift (target ^^^ source)", "lift (target ^^^ target)", "compiled XOR projection differs",
     None, None, ["bridge/Arithmetic/MutableZipRuntime.lean"]),
    ("portable-slice", "extraction/portable-slice/project.py", "extraction/portable-slice/receipt.json",
     "extraction/portable-slice/Arithmetic/Funs.lean", "bridge/Arithmetic/PortableSliceGenerated.lean",
     "if scale = 0#u64", "if scale = 1#u64", "compiled Portable slice projection differs",
     None, None, ["bridge/Arithmetic/PortableGenerated.lean",
                  "bridge/Arithmetic/PortableXorGenerated.lean",
                  "extraction/portable-xor/Arithmetic/Funs.lean"]),
    ("dense-normalization", "extraction/dense-normalization/project.py",
     "extraction/dense-normalization/receipt.json",
     "extraction/dense-normalization/Normalized/Funs.lean",
     "bridge/Arithmetic/DenseNormalizationGenerated.lean",
     "def poly.dense.normalized_len\n", "def poly.dense.normalized_len_edited\n",
     "compiled dense-normalization declarations differ", None, None,
     ["bridge/Arithmetic/DenseNormalizationTypes.lean"]),
    ("dense-coefficient", "extraction/dense-coefficient/project.py",
     "extraction/dense-coefficient/xor-coefficient/receipt.json",
     "extraction/dense-coefficient/xor-coefficient/Arithmetic/Funs.lean",
     "bridge/Arithmetic/DenseCoefficientGenerated.lean",
     "massert (index < i1)", "massert (index <= i1)",
     "compiled Dense coefficient projection differs", None, None,
     ["bridge/Arithmetic/SliceKernelTypes.lean", "bridge/Arithmetic/DenseNormalizationTypes.lean",
      "bridge/Arithmetic/DenseNormalizationGenerated.lean"]),
    ("verify-dispatch", "extraction/verify-dispatch/project.py",
     "extraction/verify-dispatch/receipt.json", "extraction/verify-dispatch/Arithmetic/Funs.lean",
     "bridge/Arithmetic/VerifyDispatchGenerated.lean",
     "if degree <= 2#usize", "if degree <= 3#usize", "compiled dispatch declarations differ",
     None, None, ["bridge/Arithmetic/VerifyDispatchRuntime.lean"]),
    ("shape-wire", "extraction/shape-admission/wire-size/project.py",
     "extraction/shape-admission/wire-size/receipt.json", "extraction/shape-admission/wire-size/Arithmetic/Funs.lean",
     "bridge/Arithmetic/ShapeWireGenerated.lean",
     "Usize.checked_mul words 8#usize", "Usize.checked_mul words 7#usize", "compiled wire-size projection differs",
     None, None, ["bridge/Arithmetic/ShapeWireRuntime.lean",
                  "extraction/shape-admission/wire-size/arithmetic.llbc"]),
    ("odd-recurrence", "extraction/odd-recurrence/project.py",
     "extraction/odd-recurrence/receipt.json", "extraction/odd-recurrence/Arithmetic/Funs.lean",
     "bridge/Arithmetic/OddRecurrenceGenerated.lean",
     "let i ← index - lag", "let i ← index + lag", "compiled recurrence projection differs",
     None, None, ["bridge/Arithmetic/SliceKernelTypes.lean"]),
    ("dense-square", "extraction/dense-square/project.py", "extraction/dense-square/receipt.json",
     "extraction/dense-square/Arithmetic/Funs.lean", "bridge/Arithmetic/DenseSquareGenerated.lean",
     "let size ← 2#usize * i", "let size ← 3#usize * i", "compiled Dense square projection differs",
     None, None, ["extraction/dense-square/refinement-receipt.json",
                  "bridge/Arithmetic/DenseSquareRuntime.lean", "bridge/Arithmetic/SliceKernelTypes.lean",
                  "bridge/Arithmetic/DenseNormalizationTypes.lean",
                  "bridge/Arithmetic/DenseNormalizationGenerated.lean"]),
    ("rebuilt-lfsr", "extraction/rebuilt-lfsr/project.py", "extraction/rebuilt-lfsr/receipt.json",
     "extraction/rebuilt-lfsr/Arithmetic/Funs.lean", "bridge/Arithmetic/RebuiltLfsrGenerated.lean",
     "let i ← index + 2#usize", "let i ← index + 1#usize", "compiled rebuilt verifier projection differs",
     None, None, ["bridge/Arithmetic/RebuiltLfsrTypes.lean", "bridge/Arithmetic/SliceKernelTypes.lean",
                  "bridge/Arithmetic/RebuiltLfsrRuntime.lean"]),
    ("affine-linear-eval", "extraction/affine-linear-eval/project.py", "extraction/affine-linear-eval/receipt.json",
     "extraction/affine-linear-eval/Arithmetic/Funs.lean", "bridge/Arithmetic/AffineLinearEvalGenerated.lean",
     "if i2 != i3", "if i2 = i3", "compiled linear evaluation projection differs",
     None, None, ["bridge/Arithmetic/SliceKernelTypes.lean"]),
    ("portable-insert", "extraction/portable-encoding/project.py", "extraction/portable-encoding/insert/receipt.json",
     "extraction/portable-encoding/insert/Arithmetic/Funs.lean", "bridge/Arithmetic/PortableInsertionGenerated.lean",
     "syndrome ^^^ power1", "syndrome ^^^ syndrome", "compiled Portable encoding projection differs",
     None, None, ["bridge/Arithmetic/SliceKernelTypes.lean", "bridge/Arithmetic/PortableGenerated.lean",
                  "bridge/Arithmetic/PortableEncodingRuntime.lean",
                  "extraction/portable-encoding/insert/refinement-receipt.json"]),
    ("portable-encode", "extraction/portable-encoding/project.py", "extraction/portable-encoding/encode/receipt.json",
     "extraction/portable-encoding/encode/Arithmetic/Funs.lean", "bridge/Arithmetic/PortableEncodingGenerated.lean",
     "if i <= 2#usize", "if i <= 1#usize", "compiled Portable encoding projection differs",
     None, None, ["bridge/Arithmetic/SliceKernelTypes.lean", "bridge/Arithmetic/PortableGenerated.lean",
                  "bridge/Arithmetic/PortableEncodingRuntime.lean",
                  "extraction/portable-encoding/encode/refinement-receipt.json"]),
    ("dense-mul-reduction", "extraction/dense-mul/project.py", "extraction/dense-mul/receipt.json",
     "extraction/dense-mul/Arithmetic/Funs.lean", "bridge/Arithmetic/DenseMulReductionGenerated.lean",
     "next_back z (some (target, product))", "next_back z none", "compiled Dense reduction projection differs",
     None, None, ["bridge/Arithmetic/SliceKernelTypes.lean", "bridge/Arithmetic/DenseNormalizationTypes.lean"]),
    ("dense-convolution", "extraction/dense-mul/project-convolution.py", "extraction/dense-mul/receipt.json",
     "extraction/dense-mul/Arithmetic/Funs.lean", "bridge/Arithmetic/DenseMulConvolutionGenerated.lean",
     "slot.lo ^^^ product.lo", "slot.lo ^^^ product.hi", "compiled Dense convolution projection differs",
     None, None, ["bridge/Arithmetic/SliceKernelTypes.lean", "bridge/Arithmetic/DenseNormalizationTypes.lean",
                  "bridge/Arithmetic/DenseMulReductionGenerated.lean", "bridge/Arithmetic/OddRecurrenceGenerated.lean",
                  "bridge/Arithmetic/DenseNormalizationGenerated.lean"]),
    ("direct-two", "extraction/direct-two/project.py", "extraction/direct-two/receipt.json",
     "extraction/direct-two/Arithmetic/Funs.lean", "bridge/Arithmetic/DirectTwoGenerated.lean",
     "if product = 0#u64", "if product = 1#u64", "compiled direct-two projection differs",
     None, None, ["bridge/Arithmetic/SliceKernelTypes.lean", "bridge/Arithmetic/DirectTwoRuntime.lean",
                  "bridge/Arithmetic/ShapeWireRuntime.lean"]),
    ("portable-horner", "extraction/portable-horner/project.py", "extraction/portable-horner/receipt.json",
     "extraction/portable-horner/Arithmetic/Funs.lean", "bridge/Arithmetic/PortableHornerGenerated.lean",
     "i ^^^ coefficient", "i ^^^ i", "compiled Portable Horner projection differs",
     None, None, ["bridge/Arithmetic/PortableHornerRuntime.lean", "bridge/Arithmetic/PortableGenerated.lean",
                  "bridge/Arithmetic/DenseNormalizationGenerated.lean", "extraction/portable-xor/Arithmetic/Funs.lean",
                  "extraction/portable-horner/refinement-receipt.json"]),
    ("x86-lane-mask", "extraction/x86-lane-mask/project.py", "extraction/x86-lane-mask/receipt.json",
     "extraction/x86-lane-mask/Arithmetic/Funs.lean", "bridge/Arithmetic/X86LaneMaskGenerated.lean",
     "8#usize - len", "7#usize - len", "compiled x86 mask projection differs",
     None, None, []),
    ("pclmul-register", "extraction/pclmul-register/project.py", "extraction/pclmul-register/receipt.json",
     "extraction/pclmul-register/Arithmetic/Funs.lean", "bridge/Arithmetic/X86PclmulGenerated.lean",
     "0#i32 mi mi1", "1#i32 mi mi1", "compiled scalar x86 projection differs",
     None, None, ["bridge/Arithmetic/X86PclmulRuntime.lean"]),
    ("avx512-register", "extraction/avx512-register/project.py", "extraction/avx512-register/receipt.json",
     "extraction/avx512-register/Arithmetic/Funs.lean", "bridge/Arithmetic/Avx512RegisterGenerated.lean",
     "17#i32 a b", "0#i32 a b", "compiled AVX-512 projection differs",
     None, None, ["bridge/Arithmetic/Avx512RegisterRuntime.lean",
                  "extraction/avx512-register/refinement-receipt.json"]),
    ("cube-root", "extraction/cube-root/project.py", "extraction/cube-root/receipt.json",
     "extraction/cube-root/Arithmetic/Funs.lean", "bridge/Arithmetic/CubeRootGenerated.lean",
     "«end» := 10#i32", "«end» := 9#i32", "compiled cube root projection differs",
     None, None, ["bridge/Arithmetic/CubeRootRuntime.lean", "bridge/Arithmetic/SliceKernelTypes.lean"]),
    ("masked-memory-diagnostic", "extraction/masked-memory/project.py", "extraction/masked-memory/receipt.json",
     "extraction/masked-memory/Arithmetic/Funs.lean", "bridge/Arithmetic/X86MaskedMemoryPureGenerated.lean",
     "ok words1", "ok words", "compiled masked memory obstruction projection differs",
     None, None, ["bridge/Arithmetic/X86LaneMaskGenerated.lean"]),
    ("pclmul-next", "extraction/pclmul-next/project.py", "extraction/pclmul-next/receipt.json",
     "extraction/pclmul-next/Arithmetic/Funs.lean", "bridge/Arithmetic/X86PclmulNextGenerated.lean",
     "lookup tupled_args 7#u32", "lookup tupled_args 6#u32", "compiled PCLMUL maps projection differs",
     None, None, ["bridge/Arithmetic/X86PclmulGenerated.lean", "bridge/Arithmetic/FrobeniusConstGenerated.lean",
                  "bridge/Arithmetic/FrobeniusTablesGenerated.lean", "bridge/Arithmetic/InverseGenerated.lean"]),
    ("x86-feature-detect", "extraction/x86-feature-detect/project.py", "extraction/x86-feature-detect/receipt.json",
     "extraction/x86-feature-detect/Arithmetic/Funs.lean", "bridge/Arithmetic/X86FeatureDetectGenerated.lean",
     "if i3 = i2", "if i3 != i2", "compiled x86 feature projection differs",
     None, None, ["bridge/Arithmetic/X86FeatureDetectTypes.lean", "bridge/Arithmetic/X86FeatureDetectRuntime.lean"]),
    ("cubic", "extraction/cubic/project.py", "extraction/cubic/receipt.json",
     "extraction/cubic/Arithmetic/Funs.lean", "bridge/Arithmetic/CubicGenerated.lean",
     "if q = 0#u64", "if q = 1#u64", "compiled cubic projection differs",
     None, None, ["bridge/Arithmetic/SliceKernelTypes.lean", "bridge/Arithmetic/CubeRootGenerated.lean"]),
    ("pclmul-slice", "extraction/pclmul-slice/project.py", "extraction/pclmul-slice/receipt.json",
     "extraction/pclmul-slice/Arithmetic/Funs.lean", "bridge/Arithmetic/X86PclmulSliceGenerated.lean",
     "lift (target ^^^ source)", "lift (target ^^^ target)", "compiled PCLMUL slice projection differs",
     None, None, ["bridge/Arithmetic/X86PclmulGenerated.lean", "bridge/Arithmetic/X86PclmulRuntime.lean",
                  "bridge/Arithmetic/MutableZipRuntime.lean", "extraction/affine-linear-eval/Arithmetic/Funs.lean"]),
    ("pclmul-horner", "extraction/pclmul-horner/project.py", "extraction/pclmul-horner/receipt.json",
     "extraction/pclmul-horner/Arithmetic/Funs.lean", "bridge/Arithmetic/X86PclmulHornerGenerated.lean",
     "if left_val = right_val", "if left_val != right_val", "compiled PCLMUL Horner projection differs",
     None, None, ["bridge/Arithmetic/X86PclmulGenerated.lean", "bridge/Arithmetic/X86PclmulRuntime.lean",
                  "bridge/Arithmetic/MutableZipRuntime.lean", "bridge/Arithmetic/DenseNormalizationGenerated.lean",
                  "bridge/Arithmetic/PortableHornerRuntime.lean", "extraction/affine-linear-eval/Arithmetic/Funs.lean",
                  "tooling/aeneas-horner-match/ended-shared-scalar.patch"]),
    ("degree-certificate", "extraction/degree-certificate/project.py", "extraction/degree-certificate/receipt.json",
     "extraction/degree-certificate/Arithmetic/Funs.lean", "bridge/Arithmetic/CertificateGenerated.lean",
     "if x = 0#u64", "if x = 1#u64", "compiled certificate projection differs",
     None, None, ["bridge/Arithmetic/CertificateRuntime.lean", "bridge/Arithmetic/RebuiltLfsrGenerated.lean",
                  "bridge/Arithmetic/SliceKernelTypes.lean", "tooling/aeneas-ended-projector/ended-projector-leaf.patch"]),
    ("work-schedule", "extraction/work-schedule/project.py", "extraction/work-schedule/receipt.json",
     "extraction/work-schedule/Arithmetic/Funs.lean", "bridge/Arithmetic/WorkScheduleGenerated.lean",
     "decode.work.mul 3#u64 val", "decode.work.mul 4#u64 val", "compiled work schedule projection differs",
     None, None, ["bridge/Arithmetic/SliceKernelTypes.lean", "bridge/Arithmetic/WorkScheduleRuntime.lean",
                  "bridge/Workmeter/Types.lean", "bridge/Workmeter/Funs.lean"]),
    ("reconstruction", "extraction/reconstruction/project.py", "extraction/reconstruction/receipt.json",
     "extraction/reconstruction/Arithmetic/Funs.lean", "bridge/Arithmetic/ReconstructionGenerated.lean",
     "let i1 ← 2#usize * capacity", "let i1 ← 3#usize * capacity", "compiled reconstruction projection differs",
     None, None, ["bridge/Arithmetic/ReconstructionTypes.lean", "bridge/Arithmetic/SliceKernelTypes.lean",
                  "bridge/Arithmetic/WorkScheduleGenerated.lean", "bridge/Workmeter/Types.lean",
                  "bridge/Workmeter/Funs.lean", "tooling/aeneas-ended-projector/receipt.json",
                  "tooling/aeneas-ended-projector/ended-projector-leaf.patch"]),
    ("affine-quartic", "extraction/affine-quartic/project.py", "extraction/affine-quartic/receipt.json",
     "extraction/affine-quartic/Arithmetic/Funs.lean", "bridge/Arithmetic/AffineQuarticGenerated.lean",
     "if c = 0#u64", "if c = 1#u64", "compiled affine projection differs",
     None, None, ["bridge/Arithmetic/CubicGenerated.lean", "bridge/Arithmetic/CertificateGenerated.lean",
                  "bridge/Arithmetic/SliceKernelTypes.lean", "bridge/Arithmetic/AffineQuarticRuntime.lean"]),
    ("quartic", "extraction/quartic/project.py", "extraction/quartic/receipt.json",
     "extraction/quartic/Arithmetic/Funs.lean", "bridge/Arithmetic/QuarticGenerated.lean",
     "if denominator = 0#u64", "if denominator = 1#u64", "compiled quartic projection differs",
     None, None, ["bridge/Arithmetic/SliceKernelTypes.lean", "bridge/Arithmetic/AffineQuarticGenerated.lean",
                  "bridge/Arithmetic/CubicGenerated.lean", "bridge/Arithmetic/CubeRootGenerated.lean",
                  "bridge/Arithmetic/CertificateGenerated.lean"]),
    ("closed-leaf", "extraction/closed-leaf/project.py", "extraction/closed-leaf/receipt.json",
     "extraction/closed-leaf/Arithmetic/Funs.lean", "bridge/Arithmetic/ClosedLeafGenerated.lean",
     "decode.roots.charge meter decode.work.Charge.LeafThree",
     "decode.roots.charge meter decode.work.Charge.LeafFour", "compiled closed-leaf projection differs",
     None, None, ["bridge/Arithmetic/SliceKernelTypes.lean", "bridge/Arithmetic/ReconstructionTypes.lean",
                  "bridge/Arithmetic/RebuiltLfsrTypes.lean", "bridge/Arithmetic/WorkScheduleGenerated.lean",
                  "bridge/Arithmetic/QuarticGenerated.lean", "bridge/Arithmetic/CertificateGenerated.lean",
                  "bridge/Workmeter/Types.lean", "bridge/Workmeter/Funs.lean"]),
    ("deg34-normalize", "extraction/deg34-normalize/project.py", "extraction/deg34-normalize/receipt.json",
     "extraction/deg34-normalize/Arithmetic/Funs.lean", "bridge/Arithmetic/NormalizeGenerated.lean",
     "Slice.index_usize cleared 5#usize", "Slice.index_usize cleared 4#usize",
     "compiled normalization projection differs", None, None, ["bridge/Arithmetic/SliceKernelTypes.lean"]),
    ("deg34-guard", "extraction/deg34-guard/project.py", "extraction/deg34-guard/receipt.json",
     "extraction/deg34-guard/Arithmetic/Funs.lean", "bridge/Arithmetic/NewtonGuardGenerated.lean",
     "if a = 0#u64", "if a = 1#u64", "compiled Newton guard projection differs",
     None, None, ["bridge/Arithmetic/SliceKernelTypes.lean",
                  "extraction/quartic/arithmetic.llbc", "extraction/quartic/Arithmetic/Funs.lean",
                  "extraction/quartic/Arithmetic/Types.lean", "extraction/quartic/Arithmetic/FunsExternal_Template.lean",
                  "extraction/deg34-normalize/arithmetic.llbc", "extraction/deg34-normalize/Arithmetic/Funs.lean",
                  "extraction/deg34-normalize/Arithmetic/Types.lean",
                  "extraction/deg34-normalize/Arithmetic/FunsExternal_Template.lean"]),
    ("bm-locator", "extraction/bm-locator/project.py", "extraction/bm-locator/receipt.json",
     "extraction/bm-locator/Arithmetic/Funs.lean", "bridge/Arithmetic/BmLocatorGenerated.lean",
     "let width ← capacity + 1#usize", "let width ← capacity + 2#usize", "compiled BM locator projection differs",
     None, None, ["extraction/bm-locator/checked-bm-locator.patch", "extraction/bm-locator/Axioms.lean",
                  "extraction/bm-locator/axioms.log", "bridge/Arithmetic/SliceKernelTypes.lean",
                  "bridge/Arithmetic/BmLocatorRuntime.lean", "bridge/Arithmetic/MutableZipRuntime.lean",
                  "bridge/Arithmetic/RebuiltLfsrRuntime.lean", "bridge/Arithmetic/PortableEncodingRuntime.lean",
                  "bridge/Arithmetic/WorkScheduleRuntime.lean", "bridge/Workmeter/FunsExternal.lean",
                  "bridge/Arithmetic/RebuiltLfsrTypes.lean", "bridge/Arithmetic/ReconstructionTypes.lean",
                  "bridge/Arithmetic/DenseNormalizationGenerated.lean", "bridge/Arithmetic/WorkScheduleGenerated.lean",
                  "bridge/Workmeter/Types.lean", "bridge/Workmeter/Funs.lean"]),
    ("degree-probe", "extraction/degree-probe/project.py", "extraction/degree-probe/receipt.json",
     "extraction/degree-probe/Arithmetic/Funs.lean", "bridge/Arithmetic/DegreeProbeGenerated.lean",
     "let stage ←", "let wrongStage ←", "compiled DegreeProbe projection differs",
     None, None, ["extraction/deg34-guard/receipt.json",
                  "extraction/deg34-guard/translator/checked-nested-slice-loan-retry.patch",
                  "bridge/Arithmetic/DegreeProbeRuntime.lean", "bridge/Arithmetic/WorkScheduleGenerated.lean",
                  "bridge/Arithmetic/NewtonGuardGenerated.lean", "bridge/Arithmetic/NormalizeGenerated.lean",
                  "bridge/Arithmetic/QuarticGenerated.lean", "bridge/Arithmetic/CertificateGenerated.lean",
                  "bridge/Arithmetic/AffineQuarticGenerated.lean", "bridge/Arithmetic/ReconstructionTypes.lean",
                  "bridge/Arithmetic/RebuiltLfsrGenerated.lean", "bridge/Workmeter/Funs.lean"]),
    ("root-setup", "extraction/root-setup/project.py", "extraction/root-setup/receipt.json",
     "extraction/root-setup/Arithmetic/Funs.lean", "bridge/Arithmetic/RootSetupGenerated.lean",
     "let i ← degree + 1#usize", "let i ← degree + 2#usize", "compiled root setup projection differs",
     None, None, ["bridge/Arithmetic/RebuiltLfsrTypes.lean", "bridge/Arithmetic/ReconstructionTypes.lean",
                  "bridge/Arithmetic/ClosedLeafGenerated.lean"]),
    ("execution-verify", "extraction/execution-verify/project.py", "extraction/execution-verify/receipt.json",
     "extraction/execution-verify/Arithmetic/Funs.lean", "bridge/Arithmetic/ExecutionVerifyGenerated.lean",
     "Charge.VerifyLfsr capacity self.budget.total r.count",
     "Charge.VerifyLfsr capacity self.budget.total 0#usize", "compiled execution verify projection differs",
     None, None, ["extraction/reconstruction/receipt.json", "bridge/Arithmetic/DegreeProbeGenerated.lean",
                  "bridge/Arithmetic/VerifyDispatchGenerated.lean", "bridge/Arithmetic/RebuiltLfsrGenerated.lean",
                  "bridge/Arithmetic/SliceKernelTypes.lean", "bridge/Arithmetic/WorkScheduleGenerated.lean",
                  "bridge/Arithmetic/ReconstructionTypes.lean", "bridge/Workmeter/Types.lean"]),
    ("root-leaf", "extraction/root-leaf/project.py", "extraction/root-leaf/receipt.json",
     "extraction/root-leaf/Arithmetic/Funs.lean", "bridge/Arithmetic/RootLeafGenerated.lean",
     "let i ← self.count + self.degree", "let i ← self.count + 1#usize", "compiled root leaf projection differs",
     None, None, ["bridge/Arithmetic/SliceKernelTypes.lean", "bridge/Arithmetic/ReconstructionTypes.lean",
                  "bridge/Arithmetic/WorkScheduleGenerated.lean", "bridge/Workmeter/Types.lean",
                  "bridge/Arithmetic/ClosedLeafGenerated.lean"]),
    ("times-x-mod", "extraction/times-x-mod/project.py", "extraction/times-x-mod/receipt.json",
     "extraction/times-x-mod/Arithmetic/Funs.lean", "bridge/Arithmetic/TimesXModGenerated.lean",
     "let i ← len - 1#usize", "let i ← len - 2#usize", "compiled modular shift projection differs",
     None, None, ["extraction/root-setup/receipt.json", "bridge/Arithmetic/SliceKernelTypes.lean",
                  "bridge/Arithmetic/TimesXModRuntime.lean"]),
    ("dense-reducer-table", "extraction/dense-reducer-table/project.py", "extraction/dense-reducer-table/receipt.json",
     "extraction/dense-reducer-table/Arithmetic/Funs.lean", "bridge/Arithmetic/DenseReducerTableGenerated.lean",
     "let rows ← degree / 2#usize", "let rows ← degree / 3#usize", "compiled Dense reducer table projection differs",
     None, None, ["extraction/root-setup/receipt.json", "extraction/portable-xor/arithmetic.llbc",
                  "bridge/Arithmetic/SliceKernelTypes.lean", "bridge/Arithmetic/TimesXModGenerated.lean",
                  "bridge/Arithmetic/TimesXModRuntime.lean", "bridge/Arithmetic/DenseReducerTableRuntime.lean"]),
    ("root-trace", "extraction/root-trace/project.py", "extraction/root-trace/receipt.json",
     "extraction/root-trace/Arithmetic/Funs.lean", "bridge/Arithmetic/RootTraceGenerated.lean",
     "buffers.basis.directions (self.splitter_seed, buffers.basis.len)",
     "buffers.basis.directions (1#u64, buffers.basis.len)", "compiled root trace projection differs",
     None, None, ["extraction/root-setup/receipt.json", "bridge/Arithmetic/SliceKernelTypes.lean",
                  "bridge/Arithmetic/RootSetupGenerated.lean", "bridge/Arithmetic/ReconstructionTypes.lean",
                  "bridge/Arithmetic/WorkScheduleGenerated.lean", "bridge/Workmeter/Types.lean"]),
]


def main():
    results = []
    originals = {}
    for label, checker, receipt_path, raw_path, active_path, before, after, changed, type_error, dictionary_error, extra_files in PROJECTIONS:
        spec = importlib.util.spec_from_file_location(label + "_projection", ROOT / checker)
        projector = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(projector)
        kwargs = {"kind": "encode"} if label == "portable-encode" else {}
        originals[label] = projector.check(**kwargs)["source_declarations_retained_verbatim"]
        receipt = json.loads((ROOT / receipt_path).read_text())
        files = [receipt_path, active_path, "bridge/Arithmetic/Types.lean", "bridge/Arithmetic/Funs.lean"]
        artifact_key = next(key for key in ("files_sha256", "artifacts", "generated") if key in receipt)
        artifacts = receipt[artifact_key]
        if isinstance(artifacts, dict):
            artifact_paths = [name if name.startswith("extraction/") else str(Path(receipt_path).parent / name)
                              for name in artifacts]
        else:
            artifact_paths = [item["path"] for item in artifacts]
        files += artifact_paths + extra_files
        cases = [
            ("compiled-body-edit", active_path, before, after, changed),
            ("raw-extraction-edit", raw_path, before, after, raw_path),
        ]
        if type_error:
            cases += [
                ("shared-type-edit", "bridge/Arithmetic/Types.lean", "BITS : Result Std.U32", "BITS : Result Std.U64", type_error),
                ("shared-dictionary-edit", "bridge/Arithmetic/Funs.lean", "BITS : Std.U32 := 64#u32", "BITS : Std.U32 := 63#u32", dictionary_error),
            ]
        if label == "wrappers":
            cases.append(("compiled-type-edit", "bridge/Arithmetic/InverseUsingTypes.lean",
                          "  T2\n", "  T1\n", "compiled wrapper type projection differs"))
        if label == "frobenius":
            cases.append(("raw-type-edit", "extraction/frobenius-const/square/Arithmetic/Types.lean",
                          "\nend bulksketch", "\ndef shadowType := Unit\nend bulksketch",
                          "raw const-square extraction drift"))
        if label == "frobenius-tables":
            cases.append(("shared-square-edit", "bridge/Arithmetic/FrobeniusConstGenerated.lean",
                          "if bit < 64#i32", "if bit < 63#i32", "shared Frobenius declaration drift"))
        if label == "slice-kernels":
            cases.append(("compiled-dictionary-edit", "bridge/Arithmetic/SliceKernelTypes.lean",
                          "structure backend.contract.Arithmetic", "structure changed.Arithmetic",
                          "compiled slice type projection differs"))
        if label == "portable-xor":
            cases.append(("backward-projection-edit", "bridge/Arithmetic/MutableZipRuntime.lean",
                          "fun state => state.fst", "fun _ => left", "scoped mutable Zip runtime mismatch"))
        if label == "dense-normalization":
            cases.append(("compiled-closure-type-edit", "bridge/Arithmetic/DenseNormalizationTypes.lean",
                          "normalized_len.closure_1 := Unit", "normalized_len.closure_1 := Bool",
                          "compiled dense-normalization types differ"))
        if label == "verify-dispatch":
            cases.append(("ceiling-rounding-edit", "bridge/Arithmetic/VerifyDispatchRuntime.lean",
                          "remainder > 0#u64", "remainder > 1#u64", "scoped dispatch runtime mismatch"))
        if label == "shape-wire":
            cases.append(("receipt-artifact-omission", receipt_path,
                          '"path": "extraction/shape-admission/wire-size/Arithmetic/Types.lean"',
                          '"path": "extraction/shape-admission/wire-size/Arithmetic/Funs.lean"',
                          "incomplete wire-size extraction receipt"))
            cases.append(("compiled-runtime-edit", "bridge/Arithmetic/ShapeWireRuntime.lean",
                          "none =>", "some _ =>", "scoped wire-size runtime mismatch"))
        if label == "dense-square":
            cases.append(("stride-zero-guard-edit", "bridge/Arithmetic/DenseSquareRuntime.lean",
                          "if stride.val = 0", "if stride.val = 1", "scoped Dense square runtime mismatch"))
            cases.append(("shared-normalization-edit", "bridge/Arithmetic/DenseNormalizationGenerated.lean",
                          "def poly.dense.normalized_len\n", "def poly.dense.normalized_len_edited\n",
                          "shared normalization declaration mismatch"))
        if label == "rebuilt-lfsr":
            cases.append(("inclusive-bound-edit", "bridge/Arithmetic/RebuiltLfsrRuntime.lean",
                          "if range.end.val < slice.length", "if range.end.val ≤ slice.length",
                          "scoped rebuilt verifier runtime mismatch"))
            cases.append(("inclusive-range-type-edit", "bridge/Arithmetic/RebuiltLfsrTypes.lean",
                          "  «end» : Idx", "  «end» : Nat",
                          "compiled rebuilt verifier inclusive range type differs"))
        if label == "dense-convolution":
            cases.append(("shared-raw-default-edit", "bridge/Arithmetic/OddRecurrenceGenerated.lean",
                          "lo := (core.default.DefaultU64.default)", "lo := 1#u64",
                          "shared RawProduct default changed"))
        if label == "direct-two":
            cases.append(("shared-any-runtime-edit", "bridge/Arithmetic/DirectTwoRuntime.lean",
                          "then", "else", "scoped direct-two runtime mismatch"))
        if label == "portable-horner":
            cases.append(("reverse-fold-runtime-edit", "bridge/Arithmetic/PortableHornerRuntime.lean",
                          "reverseFold", "forwardFold", "scoped Portable Horner runtime mismatch"))
        if label == "pclmul-register":
            cases.append(("word-selector-edit", "bridge/Arithmetic/X86PclmulRuntime.lean",
                          "getLsbD 4", "getLsbD 3", "scoped scalar x86 runtime mismatch"))
        if label == "avx512-register":
            cases.append(("carryless-runtime-edit", "bridge/Arithmetic/Avx512RegisterRuntime.lean",
                          "clmul128", "clmulPrefix", "scoped AVX-512 runtime mismatch"))
        if label == "cube-root":
            cases.append(("then-some-runtime-edit", "bridge/Arithmetic/CubeRootRuntime.lean",
                          "some", "none", "scoped cube root runtime mismatch"))
        if label == "masked-memory-diagnostic":
            cases.append(("false-native-credit", receipt_path,
                          '"native_body_proof_credit": 0', '"native_body_proof_credit": 1',
                          "masked memory diagnostic receipt changed"))
        if label == "pclmul-next":
            cases.append(("shared-register-multiply-edit", "bridge/Arithmetic/X86PclmulGenerated.lean",
                          "0#i32 mi mi1", "1#i32 mi mi1", "shared PCLMUL declaration differs"))
        if label == "x86-feature-detect":
            cases.append(("xgetbv-guard-edit", "bridge/Arithmetic/X86FeatureDetectRuntime.lean",
                          "201326592#u32", "0#u32", "scoped x86 feature runtime mismatch"))
        if label == "cubic":
            cases.append(("shared-cube-root-edit", "bridge/Arithmetic/CubeRootGenerated.lean",
                          "«end» := 10#i32", "«end» := 9#i32", "shared cube root declarations differ"))
        if label == "reconstruction":
            cases.extend([
                ("compiled-workspace-field-edit", "bridge/Arithmetic/ReconstructionTypes.lean",
                 "syndromes : Slice Std.U64", "syndromes : Slice Std.U32", "compiled reconstruction types differ"),
                ("unchecked-extraction", receipt_path, '"-checks"', '"-no-checks"',
                 "reconstruction checked and unchecked controls changed"),
                ("changed-variant", receipt_path, '"checked-ended-projector-leaf-v1"', '"checked-ended-shared-scalar-v1"',
                 "reconstruction lost checked translator provenance"),
            ])
        if label == "work-schedule":
            cases.append(("shared-meter-type-edit", "bridge/Workmeter/Types.lean",
                          "used : types.WorkUnits", "used : Std.U32", "shared work schedule type differs"))
        if label == "closed-leaf":
            cases.extend([
                ("wrong-source-revision", receipt_path, "0a5bda53f6b07fcae8acd870e2d0c4a246d207e6",
                 "0" * 40, "invalid checked closed-leaf receipt"),
                ("wrong-aeneas-command", receipt_path, receipt["aeneas_command"][0],
                 "/tmp/fake-aeneas", "closed-leaf checked replay linkage differs"),
                ("wrong-replay-input", receipt_path, receipt["aeneas_command"][-1],
                 "/tmp/unrelated/closed-leaf/arithmetic.llbc", "closed-leaf checked replay linkage differs"),
            ])
        if label == "root-setup":
            cases.append(("wrong-backend", receipt_path, '"lean"', '"fstar"',
                          "root setup checked replay differs"))
        if label == "root-leaf":
            cases.append(("wrong-backend", receipt_path, '"lean"', '"fstar"',
                          "root leaf checked replay differs"))
        if label == "execution-verify":
            cases[1] = (*cases[1][:-1], "raw execution verify artifact differs: Arithmetic/Funs.lean")
            cases.append(("wrong-backend", receipt_path, '"lean"', '"fstar"',
                          "execution verify capture or checked Lean command changed"))
        if label == "times-x-mod":
            cases.append(("wrong-backend", receipt_path, '"lean"', '"fstar"',
                          "modular shift checked capture or replay differs"))
            cases.append(("wrong-copy-offset", "bridge/Arithmetic/TimesXModRuntime.lean",
                          "destination.val + stop.val", "destination.val + stop.val + 1",
                          "modular shift runtime binding differs"))
        if label == "dense-reducer-table":
            cases.append(("wrong-backend", receipt_path, '"lean"', '"fstar"',
                          "Dense reducer checked command or control differs"))
            cases.append(("wrong-binary-digest", receipt_path, receipt["patched_binary_sha256"], "0" * 64,
                          "invalid Dense reducer table receipt"))
            cases.append(("wrong-matcher-source", receipt_path, next(iter(receipt["modified_sources"].values())),
                          "0" * 64, "invalid Dense reducer table receipt"))
            cases.append(("wrong-checkout", receipt_path, receipt["commands"]["checked"]["command"][-1],
                          "/tmp/unrelated/verification/lean/extraction/dense-reducer-table/arithmetic.llbc",
                          "Dense reducer checked command or control differs"))
        if label == "root-trace":
            cases.append(("wrong-manifest", receipt_path, receipt["charon_command"][10],
                          "--manifest-path=/tmp/unrelated/Cargo.toml", "root trace recorded Charon command differs"))
            cases.append(("wrong-backend", receipt_path, '"lean"', '"fstar"',
                          "root trace checked replay differs"))
        if label == "deg34-normalize":
            cases.append(("unchecked-original-extraction", receipt_path, '"-checks"', '"-no-checks"',
                          "normalization checked replay linkage differs"))
        for name, path, before, after, diagnostic in cases:
            name = label + "/" + name
            with tempfile.TemporaryDirectory(prefix="bulksketch-provenance-") as directory:
                shadow = Path(directory)
                if label in {"degree-certificate", "reconstruction", "affine-quartic", "quartic", "closed-leaf", "deg34-normalize", "deg34-guard",
                             "bm-locator", "degree-probe", "root-setup", "execution-verify", "root-leaf", "times-x-mod", "dense-reducer-table", "root-trace"}:
                    (shadow / "src").symlink_to(ROOT.parents[1] / "src", target_is_directory=True)
                    shadow = shadow / "verification" / "lean"
                for file in files:
                    (shadow / file).parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy2(ROOT / file, shadow / file)
                projector.check(shadow, **kwargs)
                text = (shadow / path).read_text()
                if before not in text:
                    raise RuntimeError("fixture did not find mutation target: " + name)
                (shadow / path).write_text(text.replace(before, after, 1))
                try:
                    projector.check(shadow, **kwargs)
                except ValueError as error:
                    if diagnostic not in str(error):
                        raise RuntimeError("wrong rejection for " + name + ": " + str(error)) from error
                    results.append({"case": name, "status": "expected_rejection_confirmed"})
                else:
                    raise RuntimeError("edited extraction boundary was accepted: " + name)
                optimized = subprocess.run([sys.executable, "-O", "-c",
                    "from pathlib import Path; import json,runpy,sys; "
                    "runpy.run_path(sys.argv[1])['check'](Path(sys.argv[2]), **json.loads(sys.argv[3]))",
                    str(ROOT / checker), str(shadow), json.dumps(kwargs)],
                    stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                    text=True, timeout=10)
                if optimized.returncode == 0 or diagnostic not in optimized.stdout:
                    raise RuntimeError("optimized Python did not reject " + name + ": " + optimized.stdout)
                results.append({"case": name + "-optimized-python", "status": "expected_rejection_confirmed"})
    summary = {"status": "passed", "verbatim_inverse_declarations": originals["inverse"],
               "verbatim_declarations_by_projection": originals,
               "cases": results, "native_or_production_proof_modified": False}
    output = ROOT / "bridge/audit/results/projection-fixtures.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
