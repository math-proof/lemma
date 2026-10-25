/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailBoundSkeleton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part39
import Def.StatisticalMechanics.Code.Exact3D.TailBoundSkeleton.Part2
open scoped BigOperators


namespace StatMech

namespace Exact3D

structure CutoffContributionData (d : ℕ) where
  cutoff : TailCutoff
  finiteContribution : FiniteCutoffCoordinate d cutoff → ℝ
  tailContribution : TailCoordinate d cutoff → ℝ


structure FiniteTableUpperBound {Case α : Type*} [DecidableEq Case]
    (T : RatInterval.CaseTable Case) (classify : α → Case)
    (value : α → ℝ) (bound : ℝ) : Prop where
  covers : RatInterval.CaseTable.Covers T classify
  sound : RatInterval.CaseTable.Sound T classify value
  intervalUpper_le : ∀ c, c ∈ T.cases → ((T.interval c).upper : ℝ) ≤ bound


end Exact3D
end StatMech
