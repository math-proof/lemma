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
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample.Part25


namespace StatMech

namespace Exact3D

namespace FinitePlusTailContractionExample

open InfiniteTailStableKeyPackageExample

open InfiniteTailGeneratedTablePackageExample

open InfiniteTailTableClosedBallRGPackage


noncomputable def halfThirdScalingClosedBallCertificate {radius : ℝ}
    (hradius : 0 ≤ radius) :
    FinitePlusTailClosedBallContractionCertificate 1 ℕ :=
  FinitePlusTailClosedBallContractionCertificate.ofFixedCenter
    halfThirdScalingCertificate zeroState hradius
    halfThirdScalingCertificate_map_zero


noncomputable def halfThirdScalingRadiusZeroClosedBallCertificate :
    FinitePlusTailClosedBallContractionCertificate 1 ℕ :=
  halfThirdScalingClosedBallCertificate (radius := 0) (by norm_num)


noncomputable def halfThirdScalingRadiusOneFromZeroClosedBallCertificate :
    FinitePlusTailClosedBallContractionCertificate 1 ℕ :=
  halfThirdScalingRadiusZeroClosedBallCertificate.with_larger_radius
    (radius' := 1)
    (by
      norm_num [halfThirdScalingRadiusZeroClosedBallCertificate,
        halfThirdScalingClosedBallCertificate,
        FinitePlusTailClosedBallContractionCertificate.ofFixedCenter,
        FinitePlusTailClosedBallContractionCertificate.ofResidualBound])


noncomputable def halfThirdScalingUnitClosedBallCertificate :
    FinitePlusTailClosedBallContractionCertificate 1 ℕ :=
  FinitePlusTailClosedBallContractionCertificate.ofResidualMargin
    halfThirdScalingCertificate unitCenterState
    (radius := 1)
    (by norm_num)
    (by
      convert halfThirdScalingCertificate_unitCenter_residual using 1
      norm_num [halfThirdScalingCertificate_c_eq])


noncomputable def halfThirdScalingZeroClosedBallRGPackage :
    FinitePlusTailClosedBallRGPackage 1 ℕ where
  closedBall := halfThirdScalingRadiusOneFromZeroClosedBallCertificate
  thermal := 3
  thermal_gt_one := by norm_num


noncomputable def halfThirdScalingZeroClosedBallRGCertificate :
    RGCertificate halfThirdScalingModel :=
  halfThirdScalingZeroClosedBallRGPackage.certificate
    halfThirdScalingBlockScale halfThirdScalingModel


end FinitePlusTailContractionExample
end Exact3D
end StatMech
