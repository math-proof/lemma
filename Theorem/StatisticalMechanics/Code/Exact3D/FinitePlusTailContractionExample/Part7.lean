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
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample.Part7


namespace StatMech

namespace Exact3D

namespace FinitePlusTailContractionExample

open InfiniteTailStableKeyPackageExample

open InfiniteTailGeneratedTablePackageExample

open InfiniteTailTableClosedBallRGPackage


theorem halfThirdScalingBlockBounds_zero_finiteResidual_mem :
    RatInterval.VectorMem
      (fun i =>
        halfThirdScalingBlockBounds.finiteMap zeroState i -
          zeroState.finite i)
      halfThirdScalingBlockBoundsZeroFiniteResidual := by
  intro i
  fin_cases i
  norm_num [halfThirdScalingBlockBoundsZeroFiniteResidual,
    halfThirdScalingBlockBounds,
    FinitePlusTailBlockBounds.decoupledScaling,
    FinitePlusTailBlockBounds.ofDecoupled,
    zeroState, RatInterval.pointVector, RatInterval.point,
    RatInterval.MemR]


theorem halfThirdScalingBlockBounds_zero_finiteResidual_absSum :
    RatInterval.VectorAbsSum
      halfThirdScalingBlockBoundsZeroFiniteResidual = 0 := by
  norm_num [halfThirdScalingBlockBoundsZeroFiniteResidual,
    RatInterval.VectorAbsSum_pointVector]


end FinitePlusTailContractionExample
end Exact3D
end StatMech
