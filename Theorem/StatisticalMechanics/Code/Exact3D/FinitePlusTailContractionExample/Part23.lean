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
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample.Part23


namespace StatMech

namespace Exact3D

namespace FinitePlusTailContractionExample

open InfiniteTailStableKeyPackageExample

open InfiniteTailGeneratedTablePackageExample

open InfiniteTailTableClosedBallRGPackage


theorem halfThirdScalingBlockRGCertificate_bridge_from_prefactorInputs :
    halfThirdScalingBlockRGCertificate.RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  RGCertificate.AnalyticPrefactorBridgeInputs.rgToExponentBridge
    halfThirdScalingBlockRGAnalyticPrefactorBridgeInputs


theorem halfThirdScalingBlockRGCertificate_valid_from_prefactorInputs :
    halfThirdScalingBlockRGCertificate.Valid halfThirdScalingCorrelationLength :=
  RGCertificate.AnalyticPrefactorBridgeInputs.valid_of_checks
    halfThirdScalingBlockRGAnalyticPrefactorBridgeInputs
    trivial trivial halfThirdScalingBlockRGCertificate_fixedPointEnclosure
    halfThirdScalingBlockRGCertificate_linearizationEnclosure
    halfThirdScalingBlockRGCertificate_hyperbolicSplitting trivial


theorem halfThirdScalingBlockRGCertificate_hasCriticalNu_from_prefactorInputs :
    HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength
      halfThirdScalingBlockRGCertificate.predictedExponent :=
  RGCertificate.AnalyticPrefactorBridgeInputs.hasCriticalNu
    halfThirdScalingBlockRGAnalyticPrefactorBridgeInputs


end FinitePlusTailContractionExample
end Exact3D
end StatMech
