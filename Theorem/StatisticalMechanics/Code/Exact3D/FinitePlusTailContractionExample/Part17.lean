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
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample.Part17


namespace StatMech

namespace Exact3D

namespace FinitePlusTailContractionExample

open InfiniteTailStableKeyPackageExample

open InfiniteTailGeneratedTablePackageExample

open InfiniteTailTableClosedBallRGPackage


theorem halfThirdScalingRGCertificate_bridge_from_massInputs :
    halfThirdScalingRGCertificate.RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  RGCertificate.AnalyticMassBridgeInputs.rgToExponentBridge
    halfThirdScalingAnalyticMassBridgeInputs


theorem halfThirdScalingRGCertificate_valid_from_massInputs :
    halfThirdScalingRGCertificate.Valid halfThirdScalingCorrelationLength :=
  RGCertificate.AnalyticMassBridgeInputs.valid_of_checks
    halfThirdScalingAnalyticMassBridgeInputs
    trivial trivial halfThirdScalingRGCertificate_fixedPointEnclosure
    halfThirdScalingRGCertificate_linearizationEnclosure
    halfThirdScalingRGCertificate_hyperbolicSplitting trivial


theorem halfThirdScalingRGCertificate_valid_from_massPowerLawWrapper :
    halfThirdScalingRGCertificate.Valid halfThirdScalingCorrelationLength :=
  halfThirdScalingRGCertificate.valid_of_eventually_exact_mass_power_variable_prefactor
    halfThirdScalingCorrelationLength halfThirdScalingMass
    halfThirdScalingMassPrefactor
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    halfThirdScalingMass_power
    halfThirdScalingCorrelationLength_eq_inv_mass
    trivial trivial halfThirdScalingRGCertificate_fixedPointEnclosure
    halfThirdScalingRGCertificate_linearizationEnclosure
    halfThirdScalingRGCertificate_hyperbolicSplitting trivial


theorem halfThirdScalingRGCertificate_hasCriticalNu_from_massPowerLawWrapper :
    HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength
      halfThirdScalingRGCertificate.predictedExponent :=
  halfThirdScalingRGCertificate_valid_from_massPowerLawWrapper.hasCriticalNu


theorem halfThirdScalingRGCertificate_hasCriticalNu_from_massInputs :
    HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength
      halfThirdScalingRGCertificate.predictedExponent :=
  RGCertificate.AnalyticMassBridgeInputs.hasCriticalNu
    halfThirdScalingAnalyticMassBridgeInputs


end FinitePlusTailContractionExample
end Exact3D
end StatMech
