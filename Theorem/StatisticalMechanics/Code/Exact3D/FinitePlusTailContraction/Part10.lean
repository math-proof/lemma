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
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction.Part8
open scoped BigOperators ENNReal NNReal


namespace StatMech

namespace Exact3D

namespace FinitePlusTailState

variable {n : ℕ} {α : Type*}

theorem center_mem_closedBall (center : FinitePlusTailState n α)
    {radius : ℝ} (hradius : 0 ≤ radius) :
    ClosedBall center radius center := by
  unfold ClosedBall
  simpa using hradius


theorem closedBall_mono_radius {center x : FinitePlusTailState n α}
    {radius radius' : ℝ}
    (hx : ClosedBall center radius x) (hradius : radius ≤ radius') :
    ClosedBall center radius' x :=
  le_trans hx hradius


theorem ofFinite_closedBall_iff
    {center x : Fin n → ℝ} {radius : ℝ} :
    ClosedBall (ofFinite (α := α) center) radius (ofFinite x) ↔
      FiniteContraction.ClosedBall center radius x := by
  simp [ClosedBall, FiniteContraction.ClosedBall]

end FinitePlusTailState
end Exact3D
end StatMech
