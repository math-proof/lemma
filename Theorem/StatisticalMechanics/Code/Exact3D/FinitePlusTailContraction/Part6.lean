module
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part23
public import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability.Part5
public import Structure.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction.Part2
open scoped BigOperators ENNReal NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

namespace FinitePlusTailState

variable {n : ℕ} {α : Type*}

@[ext]
theorem ext {x y : FinitePlusTailState n α}
    (hfinite : x.finite = y.finite) (htail : x.tail = y.tail) : x = y := by
  cases x
  cases y
  cases hfinite
  cases htail
  rfl

end FinitePlusTailState
end Exact3D
end StatMech
