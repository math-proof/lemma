/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdjacentCoreSeparation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardIncidentStairPatch.Part2


namespace StatMech.FrontierA

open scoped NNReal ENNReal

open Set


def KWFiniteSimplePolygon.closedEdgeCore
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (eps : ℝ) (i : Fin n) : Set ℂ :=
  AffineMap.lineMap (polygon.vertex i) (polygon.vertex (i + 1)) ''
    Icc eps (1 - eps)

end StatMech.FrontierA
