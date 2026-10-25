/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.AnalyticBridgeTarget.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailBlockRG.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBallRG.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailGeneratedTablePackageExample.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailTableClosedBallRGPackage.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailStableKeyPackageExample.Part7
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample.Part15


namespace StatMech

namespace Exact3D

namespace FinitePlusTailContractionExample

open InfiniteTailStableKeyPackageExample

open InfiniteTailGeneratedTablePackageExample

open InfiniteTailTableClosedBallRGPackage


theorem halfThirdScalingRGCertificate_bridge_from_prefactorInputs :
    halfThirdScalingRGCertificate.RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  RGCertificate.AnalyticPrefactorBridgeInputs.rgToExponentBridge
    halfThirdScalingAnalyticPrefactorBridgeInputs


theorem halfThirdScalingRGCertificate_valid_from_prefactorInputs :
    halfThirdScalingRGCertificate.Valid halfThirdScalingCorrelationLength :=
  RGCertificate.AnalyticPrefactorBridgeInputs.valid_of_checks
    halfThirdScalingAnalyticPrefactorBridgeInputs
    trivial trivial halfThirdScalingRGCertificate_fixedPointEnclosure
    halfThirdScalingRGCertificate_linearizationEnclosure
    halfThirdScalingRGCertificate_hyperbolicSplitting trivial


theorem halfThirdScalingRGCertificate_valid_from_powerLawWrapper :
    halfThirdScalingRGCertificate.Valid halfThirdScalingCorrelationLength :=
  halfThirdScalingRGCertificate.valid_of_eventually_exact_power_variable_prefactor
    halfThirdScalingCorrelationLength halfThirdScalingPrefactor
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    halfThirdScalingCorrelationLength_prefactor_power
    trivial trivial halfThirdScalingRGCertificate_fixedPointEnclosure
    halfThirdScalingRGCertificate_linearizationEnclosure
    halfThirdScalingRGCertificate_hyperbolicSplitting trivial


theorem halfThirdScalingRGCertificate_hasCriticalNu_from_powerLawWrapper :
    HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength
      halfThirdScalingRGCertificate.predictedExponent :=
  halfThirdScalingRGCertificate_valid_from_powerLawWrapper.hasCriticalNu


theorem halfThirdScalingRGCertificate_valid_from_prefactorTransport :
    halfThirdScalingRGCertificate.Valid
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) :=
  RGCertificate.Valid.mul_log_negligible_prefactor
    halfThirdScalingRGCertificate_valid_from_powerLawWrapper
    halfThirdScalingCorrelationLength_pos
    halfThirdScalingDoublePrefactor_pos
    halfThirdScalingDoublePrefactor_log_negligible


theorem halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorTransport :
    HasCriticalNu halfThirdScalingModel
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β)
      halfThirdScalingRGCertificate.predictedExponent :=
  halfThirdScalingRGCertificate_valid_from_prefactorTransport.hasCriticalNu


theorem halfThirdScalingDoubleComparison :
    ∀ᶠ β in nhdsWithin halfThirdScalingModel.betaC
        (Set.Iio halfThirdScalingModel.betaC),
      (2 : ℝ) * halfThirdScalingCorrelationLength β ≤
          halfThirdScalingDoublePrefactor β *
            halfThirdScalingCorrelationLength β ∧
        halfThirdScalingDoublePrefactor β *
            halfThirdScalingCorrelationLength β ≤
          (2 : ℝ) * halfThirdScalingCorrelationLength β :=
  Filter.Eventually.of_forall fun β => by
    simp [halfThirdScalingDoublePrefactor]


theorem halfThirdScalingRGCertificate_valid_from_constantComparison :
    halfThirdScalingRGCertificate.Valid
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) :=
  RGCertificate.Valid.of_eventually_const_mul_le_le
    halfThirdScalingRGCertificate_valid_from_powerLawWrapper
    halfThirdScalingCorrelationLength_pos
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2)
    halfThirdScalingDoubleComparison


theorem halfThirdScalingRGCertificate_hasCriticalNu_from_constantComparison :
    HasCriticalNu halfThirdScalingModel
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β)
      halfThirdScalingRGCertificate.predictedExponent :=
  halfThirdScalingRGCertificate_valid_from_constantComparison.hasCriticalNu


theorem halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorInputs :
    HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength
      halfThirdScalingRGCertificate.predictedExponent :=
  RGCertificate.AnalyticPrefactorBridgeInputs.hasCriticalNu
    halfThirdScalingAnalyticPrefactorBridgeInputs


end FinitePlusTailContractionExample
end Exact3D
end StatMech
