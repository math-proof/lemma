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
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction.Part7
open scoped BigOperators ENNReal NNReal


namespace StatMech

namespace Exact3D

namespace FinitePlusTailState

variable {n : ℕ} {α : Type*}

noncomputable def dist (x y : FinitePlusTailState n α) : ℝ :=
  FiniteContraction.l1Dist x.finite y.finite + x.tail.dist y.tail


noncomputable def finiteDist (x y : FinitePlusTailState n α) : ℝ :=
  FiniteContraction.l1Dist x.finite y.finite


noncomputable def tailDist (x y : FinitePlusTailState n α) : ℝ :=
  x.tail.dist y.tail


end FinitePlusTailState
end Exact3D
end StatMech
