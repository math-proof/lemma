import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardVertexEdgeSeparation
open StatMech StatMech.FrontierA


/--
[KWVertexEdgeNonincident.symm_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardVertexEdgeSeparation.lean)
-/
@[path]
private lemma symm_endpoint_eq
  {n : ℕ}
  [NeZero n]
  {v j : Fin n}
-- given
  (h : KWVertexEdgeNonincident v j) :
-- imply
  v ≠ j ∧ v ≠ j + 1 := by
-- proof
  apply StatMech.FrontierA.KWVertexEdgeNonincident.symm_endpoint h

/--
[KWFiniteSimplePolygon.vertex_not_mem_closedEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardVertexEdgeSeparation.lean)
-/
@[path]
private lemma vertex_not_mem_closedEdge_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {v j : Fin n}
-- given
  (hvj : v ≠ j)
  (hvjs : v ≠ j + 1) :
-- imply
  polygon.vertex v ∉ polygon.closedEdge j := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.vertex_not_mem_closedEdge polygon hvj hvjs

/--
[KWFiniteSimplePolygon.singleton_vertex_disjoint_closedEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardVertexEdgeSeparation.lean)
-/
@[path]
private lemma singleton_vertex_disjoint_closedEdge_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {v j : Fin n}
-- given
  (hvj : v ≠ j)
  (hvjs : v ≠ j + 1) :
-- imply
  Disjoint ({polygon.vertex v} : Set ℂ) (polygon.closedEdge j) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.singleton_vertex_disjoint_closedEdge polygon hvj hvjs

/--
[KWFiniteSimplePolygon.singleton_vertex_disjoint_closedEdge_of_nonincident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardVertexEdgeSeparation.lean)
-/
@[path]
private lemma singleton_vertex_disjoint_closedEdge_of_nonincident_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {v j : Fin n}
-- given
  (hvj : KWVertexEdgeNonincident v j) :
-- imply
  Disjoint ({polygon.vertex v} : Set ℂ) (polygon.closedEdge j) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.singleton_vertex_disjoint_closedEdge_of_nonincident polygon hvj

/--
[KWFiniteSimplePolygon.exists_uniform_vertex_edge_separation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardVertexEdgeSeparation.lean)
-/
@[path]
private lemma exists_uniform_vertex_edge_separation_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n} :
-- imply
  ∃ r : ℝ≥0, 0 < r ∧ ∀ v j : Fin n, v ≠ j → v ≠ j + 1 → ∀ y ∈ polygon.closedEdge j, (r : ℝ) < dist (polygon.vertex v) y := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_uniform_vertex_edge_separation polygon

/--
[KWFiniteSimplePolygon.vertexBall_disjoint_closedEdgeTube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardVertexEdgeSeparation.lean)
-/
@[path]
private lemma vertexBall_disjoint_closedEdgeTube_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {r : ℝ≥0}
  {v j : Fin n}
-- given
  (hsep : ∀ v j : Fin n, v ≠ j → v ≠ j + 1 → ∀ y ∈ polygon.closedEdge j, (r : ℝ) < dist (polygon.vertex v) y)
  (hvj : v ≠ j)
  (hvjs : v ≠ j + 1) :
-- imply
  Disjoint (Metric.ball (polygon.vertex v) ((r : ℝ) / 2)) (polygon.closedEdgeTube (r / 2) j) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.vertexBall_disjoint_closedEdgeTube polygon hsep hvj hvjs


-- created on 2026-10-23
