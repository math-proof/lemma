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
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample.Part28


namespace StatMech

namespace Exact3D

namespace FinitePlusTailContractionExample

open InfiniteTailStableKeyPackageExample

open InfiniteTailGeneratedTablePackageExample

open InfiniteTailTableClosedBallRGPackage


theorem halfThirdScalingUnitClosedBallRGPackage_relaxedResidual_residual_eq :
    halfThirdScalingUnitClosedBallRGPackage_relaxedResidual.closedBall.residual =
      (3 : ℝ) / 4 :=
  rfl


theorem
    halfThirdScalingUnitClosedBallRGPackage_relaxedResidual_predictedExponent_eq :
    (halfThirdScalingUnitClosedBallRGPackage_relaxedResidual.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent =
        predictedNu halfThirdScalingBlockScale 3 :=
  FinitePlusTailClosedBallRGPackage.certificate_predictedExponent_eq
    halfThirdScalingUnitClosedBallRGPackage_relaxedResidual
    halfThirdScalingBlockScale halfThirdScalingModel


theorem halfThirdScalingUnitClosedBallRGPackage_relaxedResidual_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu halfThirdScalingModel correlationLength
        (halfThirdScalingUnitClosedBallRGPackage_relaxedRadius.certificate
          halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent) :
    HasCriticalNu halfThirdScalingModel correlationLength
      (halfThirdScalingUnitClosedBallRGPackage_relaxedResidual.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
  simpa [halfThirdScalingUnitClosedBallRGPackage_relaxedResidual] using
    FinitePlusTailClosedBallRGPackage.with_larger_residual_hasCriticalNu
      halfThirdScalingUnitClosedBallRGPackage_relaxedRadius
      (residual' := (3 : ℝ) / 4)
      (by
        norm_num [halfThirdScalingUnitClosedBallRGPackage_relaxedRadius,
          halfThirdScalingUnitClosedBallRGPackage,
          halfThirdScalingUnitClosedBallCertificate,
          FinitePlusTailClosedBallContractionCertificate.ofResidualMargin,
          FinitePlusTailClosedBallContractionCertificate.ofResidualBound,
          halfThirdScalingCertificate_c_eq])
      (by
        norm_num [halfThirdScalingUnitClosedBallRGPackage_relaxedRadius,
          halfThirdScalingUnitClosedBallRGPackage,
          halfThirdScalingUnitClosedBallCertificate,
          FinitePlusTailClosedBallContractionCertificate.ofResidualMargin,
          FinitePlusTailClosedBallContractionCertificate.ofResidualBound,
          halfThirdScalingCertificate_c_eq])
      halfThirdScalingBlockScale halfThirdScalingModel hν


end FinitePlusTailContractionExample
end Exact3D
end StatMech
