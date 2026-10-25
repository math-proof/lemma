/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailBoundSkeleton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part39
import Structure.StatisticalMechanics.Code.Exact3D.TailBoundSkeleton.Part2
open scoped BigOperators


namespace StatMech

namespace Exact3D

theorem finite_le_of_tableUpperBound {Case α : Type*} [DecidableEq Case]
    {T : RatInterval.CaseTable Case} {classify : α → Case}
    {value : α → ℝ} {bound : ℝ}
    (h : FiniteTableUpperBound T classify value bound) (a : α) :
    value a ≤ bound :=
  le_trans (h.sound a).2 (h.intervalUpper_le (classify a) (h.covers a))


end Exact3D
end StatMech
