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
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample.Part51


namespace StatMech

namespace Exact3D

namespace FinitePlusTailContractionExample

open InfiniteTailStableKeyPackageExample

open InfiniteTailGeneratedTablePackageExample

open InfiniteTailTableClosedBallRGPackage


theorem genBoundedCaseRadiusFive_radius_eq :
    genBoundedCaseRadiusFive.closedBallRadius = 5 :=
  rfl


theorem genBoundedCaseRadiusFive_residual_eq :
    genBoundedCaseRadiusFive.closedBallResidual = (1 : ℝ) / 2 :=
  by
    norm_num [genBoundedCaseRadiusFive,
      genBoundedCaseTableClosedBallRGPackage,
      halfThirdScalingUnitClosedBallRGPackage,
      halfThirdScalingUnitClosedBallCertificate,
      InfiniteTailTableClosedBallRGPackage.with_larger_closedBallRadius,
      InfiniteTailTableClosedBallRGPackage.closedBallResidual,
      FinitePlusTailClosedBallRGPackage.with_larger_radius,
      FinitePlusTailClosedBallContractionCertificate.with_larger_radius,
      FinitePlusTailClosedBallContractionCertificate.ofResidualMargin,
      FinitePlusTailClosedBallContractionCertificate.ofResidualBound,
      halfThirdScalingCertificate_c_eq]


theorem genBoundedCaseRadiusFive_contraction_c_eq :
    genBoundedCaseRadiusFive.closedBallContraction.c = (1 : ℝ) / 2 :=
  by
    norm_num [genBoundedCaseRadiusFive,
      genBoundedCaseTableClosedBallRGPackage,
      halfThirdScalingUnitClosedBallRGPackage,
      halfThirdScalingUnitClosedBallCertificate,
      InfiniteTailTableClosedBallRGPackage.with_larger_closedBallRadius,
      InfiniteTailTableClosedBallRGPackage.closedBallContraction,
      FinitePlusTailClosedBallRGPackage.with_larger_radius,
      FinitePlusTailClosedBallContractionCertificate.with_larger_radius,
      FinitePlusTailClosedBallContractionCertificate.ofResidualMargin,
      FinitePlusTailClosedBallContractionCertificate.ofResidualBound,
      halfThirdScalingCertificate_c_eq]


end FinitePlusTailContractionExample
end Exact3D
end StatMech
