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
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample.Part26


namespace StatMech

namespace Exact3D

namespace FinitePlusTailContractionExample

open InfiniteTailStableKeyPackageExample

open InfiniteTailGeneratedTablePackageExample

open InfiniteTailTableClosedBallRGPackage


noncomputable def halfThirdScalingUnitClosedBallRGPackage :
    FinitePlusTailClosedBallRGPackage 1 ℕ where
  closedBall := halfThirdScalingUnitClosedBallCertificate
  thermal := 3
  thermal_gt_one := by norm_num


noncomputable def halfThirdScalingUnitClosedBallRGPackage_relaxedRadius :
    FinitePlusTailClosedBallRGPackage 1 ℕ :=
  halfThirdScalingUnitClosedBallRGPackage.with_larger_radius
    (radius' := 2)
    (by
      norm_num [halfThirdScalingUnitClosedBallRGPackage,
        halfThirdScalingUnitClosedBallCertificate,
        FinitePlusTailClosedBallContractionCertificate.ofResidualMargin,
        FinitePlusTailClosedBallContractionCertificate.ofResidualBound])


end FinitePlusTailContractionExample
end Exact3D
end StatMech
