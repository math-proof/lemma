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
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample.Part27


namespace StatMech

namespace Exact3D

namespace FinitePlusTailContractionExample

open InfiniteTailStableKeyPackageExample

open InfiniteTailGeneratedTablePackageExample

open InfiniteTailTableClosedBallRGPackage


theorem halfThirdScalingUnitClosedBallRGPackage_relaxedRadius_radius_eq :
    halfThirdScalingUnitClosedBallRGPackage_relaxedRadius.closedBall.radius =
      2 :=
  rfl


theorem halfThirdScalingUnitClosedBallRGPackage_relaxedRadius_thermal_eq :
    halfThirdScalingUnitClosedBallRGPackage_relaxedRadius.thermal = 3 :=
  rfl


theorem
    halfThirdScalingUnitClosedBallRGPackage_relaxedRadius_predictedExponent_eq :
    (halfThirdScalingUnitClosedBallRGPackage_relaxedRadius.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent =
        predictedNu halfThirdScalingBlockScale 3 :=
  FinitePlusTailClosedBallRGPackage.certificate_predictedExponent_eq
    halfThirdScalingUnitClosedBallRGPackage_relaxedRadius
    halfThirdScalingBlockScale halfThirdScalingModel


theorem halfThirdScalingUnitClosedBallRGPackage_relaxedRadius_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu halfThirdScalingModel correlationLength
        (halfThirdScalingUnitClosedBallRGPackage.certificate
          halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent) :
    HasCriticalNu halfThirdScalingModel correlationLength
      (halfThirdScalingUnitClosedBallRGPackage_relaxedRadius.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
  simpa [halfThirdScalingUnitClosedBallRGPackage_relaxedRadius] using
    halfThirdScalingUnitClosedBallRGPackage.with_larger_radius_hasCriticalNu
      (radius' := 2)
      (by
        norm_num [halfThirdScalingUnitClosedBallRGPackage,
          halfThirdScalingUnitClosedBallCertificate,
          FinitePlusTailClosedBallContractionCertificate.ofResidualMargin,
          FinitePlusTailClosedBallContractionCertificate.ofResidualBound])
      halfThirdScalingBlockScale halfThirdScalingModel hν


end FinitePlusTailContractionExample
end Exact3D
end StatMech
