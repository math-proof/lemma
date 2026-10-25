/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCoreTubes.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdjacentCoreSeparation


namespace StatMech.FrontierA

open scoped NNReal ENNReal Convex Pointwise

open Set

def KWFiniteSimplePolygon.closedEdgeCoreTube
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (eps : ℝ) (r : ℝ≥0) (i : Fin n) : Set ℂ :=
  {z | ∃ x ∈ polygon.closedEdgeCore eps i, dist z x < r}

end StatMech.FrontierA
