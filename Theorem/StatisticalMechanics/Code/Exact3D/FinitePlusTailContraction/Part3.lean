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
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction.Part3
open scoped BigOperators ENNReal NNReal


namespace StatMech

namespace Exact3D

namespace SummableTail

variable {α : Type*}


theorem dist_scale (c : ℝ) (u v : SummableTail α) :
    (scale c u).dist (scale c v) = |c| * u.dist v := by
  calc
    (scale c u).dist (scale c v) =
        ∑' a, |c| * |u.coeff a - v.coeff a| := by
      refine tsum_congr fun a => ?_
      have h :
          c * u.coeff a - c * v.coeff a =
            c * (u.coeff a - v.coeff a) := by
        ring
      simp [scale, h, abs_mul]
    _ = |c| * u.dist v := by
      rw [tsum_mul_left]
      rfl


theorem norm_scale (c : ℝ) (u : SummableTail α) :
    (scale c u).norm = |c| * u.norm := by
  calc
    (scale c u).norm =
        ∑' a, |c| * |u.coeff a| := by
      refine tsum_congr fun a => ?_
      simp [scale, abs_mul]
    _ = |c| * u.norm := by
      rw [tsum_mul_left]
      rfl


end SummableTail
end Exact3D
end StatMech
