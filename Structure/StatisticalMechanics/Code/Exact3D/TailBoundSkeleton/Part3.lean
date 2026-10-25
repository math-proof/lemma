/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailBoundSkeleton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part39
import Theorem.StatisticalMechanics.Code.Exact3D.TailBoundSkeleton
open scoped BigOperators


namespace StatMech

namespace Exact3D

structure ContributionSplit (α : Type*) where
  finiteContribution : α → ℝ
  tailContribution : α → ℝ
  totalContribution : α → ℝ

end Exact3D
end StatMech
