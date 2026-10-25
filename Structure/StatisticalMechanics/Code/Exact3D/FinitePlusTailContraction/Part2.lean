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
import Instance.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction.Part3
open scoped BigOperators ENNReal NNReal


namespace StatMech

namespace Exact3D

structure FinitePlusTailState (n : ℕ) (α : Type*) where
  finite : Fin n → ℝ
  tail : SummableTail α

end Exact3D
end StatMech
