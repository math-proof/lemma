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
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample.Part17


namespace StatMech

namespace Exact3D

namespace FinitePlusTailContractionExample

open InfiniteTailStableKeyPackageExample

open InfiniteTailGeneratedTablePackageExample

open InfiniteTailTableClosedBallRGPackage


noncomputable def halfThirdScalingBlockRGPackage :
    FinitePlusTailBlockRGPackage 1 ℕ where
  blockBounds := halfThirdScalingBlockBounds
  c := (1 : ℝ) / 2
  c_nonneg := by norm_num
  c_lt_one := by norm_num
  finite_column_sum_le := halfThirdScalingBlockBounds_finite_column
  tail_column_sum_le := halfThirdScalingBlockBounds_tail_column
  origin_fixed := halfThirdScalingBlockBounds_map_origin
  thermal := 3
  thermal_gt_one := by norm_num
  stable_dominated := by norm_num


end FinitePlusTailContractionExample
end Exact3D
end StatMech
