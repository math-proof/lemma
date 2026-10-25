/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardVertexNeighborhood.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardVertexEdgeSeparation
import Structure.StatisticalMechanics.Code.FrontierA.KacWardVertexNeighborhood


namespace StatMech.FrontierA

open scoped NNReal

open Set


def KWVertexNeighborhoodData.vertexBall
    {n : ℕ} [NeZero n] {polygon : KWFiniteSimplePolygon n}
    (data : KWVertexNeighborhoodData polygon) (i : Fin n) : Set ℂ :=
  Metric.ball (polygon.vertex i) ((data.scale : ℝ) / 2)


def KWVertexNeighborhoodData.edgeTube
    {n : ℕ} [NeZero n] {polygon : KWFiniteSimplePolygon n}
    (data : KWVertexNeighborhoodData polygon) (i : Fin n) : Set ℂ :=
  polygon.closedEdgeTube (data.scale / 2) i

end StatMech.FrontierA
