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
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample.Part26


namespace StatMech

namespace Exact3D

namespace FinitePlusTailContractionExample

open InfiniteTailStableKeyPackageExample

open InfiniteTailGeneratedTablePackageExample

open InfiniteTailTableClosedBallRGPackage


theorem halfThirdScalingZeroClosedBallRGCertificate_fixedPointEnclosure :
    halfThirdScalingZeroClosedBallRGCertificate.FixedPointEnclosure := by
  simpa [halfThirdScalingZeroClosedBallRGCertificate] using
    FinitePlusTailClosedBallContractionCertificate.certificate_fixedPointEnclosure
      halfThirdScalingRadiusOneFromZeroClosedBallCertificate
      halfThirdScalingBlockScale halfThirdScalingModel 3 (by norm_num)


theorem halfThirdScalingZeroClosedBallRGCertificate_fixedPoint_mem :
    FinitePlusTailState.ClosedBall zeroState 1
      halfThirdScalingZeroClosedBallRGCertificate.fixedPointData.fixedPoint := by
  simpa [halfThirdScalingZeroClosedBallRGCertificate,
    halfThirdScalingRadiusOneFromZeroClosedBallCertificate,
    halfThirdScalingRadiusZeroClosedBallCertificate,
    halfThirdScalingClosedBallCertificate] using
    FinitePlusTailClosedBallContractionCertificate.certificate_fixedPoint_mem_closedBall
      halfThirdScalingRadiusOneFromZeroClosedBallCertificate
      halfThirdScalingBlockScale halfThirdScalingModel 3 (by norm_num)


theorem halfThirdScalingZeroClosedBallRGCertificate_iterate_mem
    {x : halfThirdScalingZeroClosedBallRGCertificate.H.carrier}
    (hx : FinitePlusTailState.ClosedBall zeroState 1 x) (k : ℕ) :
    FinitePlusTailState.ClosedBall zeroState 1
      (((halfThirdScalingZeroClosedBallRGCertificate.R.map)^[k]) x) := by
  simpa [halfThirdScalingZeroClosedBallRGCertificate,
    halfThirdScalingRadiusOneFromZeroClosedBallCertificate,
    halfThirdScalingRadiusZeroClosedBallCertificate,
    halfThirdScalingClosedBallCertificate] using
    FinitePlusTailClosedBallContractionCertificate.certificate_iterate_mem_closedBall
      halfThirdScalingRadiusOneFromZeroClosedBallCertificate
      halfThirdScalingBlockScale halfThirdScalingModel 3 (by norm_num) hx k


theorem halfThirdScalingZeroClosedBallRGPackage_fixedPoint_mem :
    FinitePlusTailState.ClosedBall
      halfThirdScalingZeroClosedBallRGPackage.closedBall.center
      halfThirdScalingZeroClosedBallRGPackage.closedBall.radius
      (halfThirdScalingZeroClosedBallRGPackage.certificate
        halfThirdScalingBlockScale
        halfThirdScalingModel).fixedPointData.fixedPoint :=
  halfThirdScalingZeroClosedBallRGPackage.certificate_fixedPoint_mem_closedBall
    halfThirdScalingBlockScale halfThirdScalingModel


theorem halfThirdScalingZeroClosedBallRGPackage_iterate_mem
    {x :
      (halfThirdScalingZeroClosedBallRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).H.carrier}
    (hx :
      FinitePlusTailState.ClosedBall
        halfThirdScalingZeroClosedBallRGPackage.closedBall.center
        halfThirdScalingZeroClosedBallRGPackage.closedBall.radius x)
    (k : ℕ) :
    FinitePlusTailState.ClosedBall
      halfThirdScalingZeroClosedBallRGPackage.closedBall.center
      halfThirdScalingZeroClosedBallRGPackage.closedBall.radius
      ((((halfThirdScalingZeroClosedBallRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).R.map)^[k]) x) :=
  halfThirdScalingZeroClosedBallRGPackage.certificate_iterate_mem_closedBall
    halfThirdScalingBlockScale halfThirdScalingModel hx k


theorem halfThirdScalingZeroClosedBallRGPackage_thermalEigenvalue_eq :
    (halfThirdScalingZeroClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).thermalEigenvalue =
        3 :=
  halfThirdScalingZeroClosedBallRGPackage.certificate_thermalEigenvalue_eq
    halfThirdScalingBlockScale halfThirdScalingModel


theorem halfThirdScalingZeroClosedBallRGPackage_scale_eq :
    (halfThirdScalingZeroClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).scale =
        halfThirdScalingBlockScale :=
  halfThirdScalingZeroClosedBallRGPackage.certificate_scale_eq
    halfThirdScalingBlockScale halfThirdScalingModel


theorem halfThirdScalingZeroClosedBallRGPackage_predictedExponent_eq :
    (halfThirdScalingZeroClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent =
        predictedNu halfThirdScalingBlockScale 3 :=
  halfThirdScalingZeroClosedBallRGPackage.certificate_predictedExponent_eq
    halfThirdScalingBlockScale halfThirdScalingModel


end FinitePlusTailContractionExample
end Exact3D
end StatMech
