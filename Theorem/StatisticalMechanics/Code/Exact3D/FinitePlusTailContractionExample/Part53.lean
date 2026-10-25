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
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample.Part54


namespace StatMech

namespace Exact3D

namespace FinitePlusTailContractionExample

open InfiniteTailStableKeyPackageExample

open InfiniteTailGeneratedTablePackageExample

open InfiniteTailTableClosedBallRGPackage


theorem genCubicClassRadiusFive_radius_eq :
    genCubicClassRadiusFive.closedBallRadius = 5 :=
  rfl


theorem genCubicClassRadiusFive_residual_eq :
    genCubicClassRadiusFive.closedBallResidual = (1 : ℝ) / 2 :=
  by
    norm_num [genCubicClassRadiusFive,
      genCubicClassTableClosedBallRGPackage,
      halfThirdScalingUnitClosedBallRGPackage,
      halfThirdScalingUnitClosedBallCertificate,
      InfiniteTailTableClosedBallRGPackage.with_larger_closedBallRadius,
      InfiniteTailTableClosedBallRGPackage.closedBallResidual,
      FinitePlusTailClosedBallRGPackage.with_larger_radius,
      FinitePlusTailClosedBallContractionCertificate.with_larger_radius,
      FinitePlusTailClosedBallContractionCertificate.ofResidualMargin,
      FinitePlusTailClosedBallContractionCertificate.ofResidualBound,
      halfThirdScalingCertificate_c_eq]


theorem genCubicClassRadiusFive_contraction_c_eq :
    genCubicClassRadiusFive.closedBallContraction.c = (1 : ℝ) / 2 :=
  by
    norm_num [genCubicClassRadiusFive,
      genCubicClassTableClosedBallRGPackage,
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
