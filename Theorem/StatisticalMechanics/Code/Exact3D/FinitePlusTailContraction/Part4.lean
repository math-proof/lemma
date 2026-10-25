/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Normed.Lp.lpSpace
import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part23
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability.Part5
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction.Part4
open scoped BigOperators ENNReal NNReal


namespace StatMech

namespace Exact3D

namespace SummableTail

variable {α : Type*}


theorem norm_toLpOne_sub (u v : SummableTail α) :
    ‖toLpOne u - toLpOne v‖ = u.dist v := by
  rw [lp.norm_eq_tsum_rpow (p := (1 : ℝ≥0∞)) (by norm_num)]
  change
    (∑' i : α, ‖(toLpOne u - toLpOne v) i‖ ^ (1 : ℝ)) ^
        (1 / (1 : ℝ)) =
      u.dist v
  norm_num
  unfold dist
  refine tsum_congr fun i => ?_
  change |u.coeff i - v.coeff i| = |u.coeff i - v.coeff i|
  rfl


theorem dist_toLpOne (u v : SummableTail α) :
    Dist.dist (toLpOne u) (toLpOne v) = u.dist v := by
  rw [dist_eq_norm]
  exact norm_toLpOne_sub u v


end SummableTail
end Exact3D
end StatMech
