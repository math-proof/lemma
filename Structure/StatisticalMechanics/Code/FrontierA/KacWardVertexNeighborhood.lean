/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardVertexNeighborhood.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardVertexEdgeSeparation


namespace StatMech.FrontierA

open scoped NNReal

open Set


structure KWVertexNeighborhoodData {n : ℕ} [NeZero n]
    (polygon : KWFiniteSimplePolygon n) where
  scale : ℝ≥0
  scale_pos : 0 < scale
  vertex_separated : ∀ i j : Fin n, i ≠ j →
    (scale : ℝ) < dist (polygon.vertex i) (polygon.vertex j)
  vertex_edge_separated : ∀ v j : Fin n, KWVertexEdgeNonincident v j →
    ∀ y ∈ polygon.closedEdge j,
      (scale : ℝ) < dist (polygon.vertex v) y


end StatMech.FrontierA
