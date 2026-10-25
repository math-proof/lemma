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
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample.Part6


namespace StatMech

namespace Exact3D

namespace FinitePlusTailContractionExample

open InfiniteTailStableKeyPackageExample

open InfiniteTailGeneratedTablePackageExample

open InfiniteTailTableClosedBallRGPackage


theorem halfThirdScalingCertificate_map_zero :
    halfThirdScalingCertificate.map zeroState = zeroState := by
  ext i <;>
    simp [zeroState, halfThirdScalingCertificate,
      FinitePlusTailLipschitzCertificate.decoupledScaling,
      FinitePlusTailLipschitzCertificate.ofDecoupled,
      SummableTail.scale]


theorem halfThirdScalingCertificate_map_origin :
    halfThirdScalingCertificate.map
        (FinitePlusTailState.origin : FinitePlusTailState 1 ℕ) =
      FinitePlusTailState.origin := by
  simpa [zeroState, FinitePlusTailState.origin] using
    halfThirdScalingCertificate_map_zero


theorem halfThirdScalingBlockBounds_map_zero :
    halfThirdScalingBlockBounds.map zeroState = zeroState := by
  ext i <;>
    simp [zeroState, halfThirdScalingBlockBounds,
      FinitePlusTailBlockBounds.map,
      FinitePlusTailBlockBounds.decoupledScaling,
      FinitePlusTailBlockBounds.ofDecoupled,
      SummableTail.scale]


theorem halfThirdScalingBlockBounds_map_origin :
    halfThirdScalingBlockBounds.map
        (FinitePlusTailState.origin : FinitePlusTailState 1 ℕ) =
      FinitePlusTailState.origin := by
  simpa [zeroState, FinitePlusTailState.origin] using
    halfThirdScalingBlockBounds_map_zero


theorem halfThirdScalingBlockBounds_zero_residual :
    (halfThirdScalingBlockBounds.map zeroState).dist zeroState ≤ 0 := by
  rw [halfThirdScalingBlockBounds_map_zero, FinitePlusTailState.dist_self]


theorem halfThirdScalingBlockBounds_zero_finiteResidual :
    FiniteContraction.l1Dist
      (halfThirdScalingBlockBounds.finiteMap zeroState) zeroState.finite ≤ 0 := by
  norm_num [halfThirdScalingBlockBounds,
    FinitePlusTailBlockBounds.decoupledScaling,
    FinitePlusTailBlockBounds.ofDecoupled,
    zeroState, FiniteContraction.l1Dist, RatInterval.supNormVec]


theorem halfThirdScalingBlockBounds_zero_tailResidual :
    (halfThirdScalingBlockBounds.tailMap zeroState).dist zeroState.tail ≤ 0 := by
  simp [halfThirdScalingBlockBounds,
    FinitePlusTailBlockBounds.decoupledScaling,
    FinitePlusTailBlockBounds.ofDecoupled,
    zeroState, SummableTail.scale, SummableTail.dist]


end FinitePlusTailContractionExample
end Exact3D
end StatMech
