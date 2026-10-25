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
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction.Part2
open scoped BigOperators ENNReal NNReal


namespace StatMech

namespace Exact3D

namespace SummableTail

variable {α : Type*}


noncomputable def scale (c : ℝ) (u : SummableTail α) :
    SummableTail α where
  coeff := fun a => c * u.coeff a
  summable_abs := by
    have h := u.summable_abs.mul_left |c|
    refine h.congr ?_
    intro a
    simp [abs_mul]


end SummableTail
end Exact3D
end StatMech
