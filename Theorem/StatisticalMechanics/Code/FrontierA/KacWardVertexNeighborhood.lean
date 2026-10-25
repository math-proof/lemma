/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardVertexNeighborhood.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardVertexEdgeSeparation
import Def.StatisticalMechanics.Code.FrontierA.KacWardVertexNeighborhood


namespace StatMech.FrontierA

open scoped NNReal

open Set


theorem KWFiniteSimplePolygon.exists_vertexNeighborhoodData
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) :
    Nonempty (KWVertexNeighborhoodData polygon) := by
  obtain ⟨rv, hrv, hv⟩ := polygon.exists_uniform_vertex_separation
  obtain ⟨re, hre, he⟩ := polygon.exists_uniform_vertex_edge_separation
  refine ⟨⟨min rv re, lt_min hrv hre, ?_, ?_⟩⟩
  · intro i j hij
    have hmin : ((min rv re : ℝ≥0) : ℝ) ≤ (rv : ℝ) := by
      exact_mod_cast min_le_left rv re
    exact hmin.trans_lt (hv i j hij)
  · intro v j hvj y hy
    have hmin : ((min rv re : ℝ≥0) : ℝ) ≤ (re : ℝ) := by
      exact_mod_cast min_le_right rv re
    exact hmin.trans_lt (he v j hvj.1 hvj.2 y hy)

theorem KWVertexNeighborhoodData.vertexBall_disjoint
    {n : ℕ} [NeZero n] {polygon : KWFiniteSimplePolygon n}
    (data : KWVertexNeighborhoodData polygon)
    {i j : Fin n} (hij : i ≠ j) :
    Disjoint (data.vertexBall i) (data.vertexBall j) := by
  rw [Set.disjoint_left]
  intro z hzi hzj
  have hiz : dist (polygon.vertex i) z < (data.scale : ℝ) / 2 :=
    Metric.mem_ball'.mp hzi
  have hzj' : dist z (polygon.vertex j) < (data.scale : ℝ) / 2 := by
    simpa only [dist_comm z (polygon.vertex j)] using Metric.mem_ball'.mp hzj
  have hij' := data.vertex_separated i j hij
  have htriangle : dist (polygon.vertex i) (polygon.vertex j) ≤
      dist (polygon.vertex i) z + dist z (polygon.vertex j) :=
    dist_triangle _ _ _
  linarith

theorem KWVertexNeighborhoodData.vertexBall_disjoint_edgeTube
    {n : ℕ} [NeZero n] {polygon : KWFiniteSimplePolygon n}
    (data : KWVertexNeighborhoodData polygon)
    {v j : Fin n} (hvj : KWVertexEdgeNonincident v j) :
    Disjoint (data.vertexBall v) (data.edgeTube j) := by
  exact polygon.vertexBall_disjoint_closedEdgeTube
    (fun v j hvj hvjs ↦ data.vertex_edge_separated v j ⟨hvj, hvjs⟩)
    hvj.1 hvj.2

end StatMech.FrontierA
