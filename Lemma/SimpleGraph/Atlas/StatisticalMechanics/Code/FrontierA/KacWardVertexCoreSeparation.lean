import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardVertexCoreSeparation
open StatMech StatMech.FrontierA


/--
[KWFiniteSimplePolygon.singleton_vertex_disjoint_closedEdgeCore](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardVertexCoreSeparation.lean)
-/
@[path]
private lemma singleton_vertex_disjoint_closedEdgeCore_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {eps : ℝ}
  {v i : Fin n}
-- given
  (heps : 0 < eps ∧ eps < 1 / 2) :
-- imply
  Disjoint ({polygon.vertex v} : Set ℂ) (polygon.closedEdgeCore eps i) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.singleton_vertex_disjoint_closedEdgeCore polygon heps v i

/--
[KWFiniteSimplePolygon.exists_uniform_vertex_core_separation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardVertexCoreSeparation.lean)
-/
@[path]
private lemma exists_uniform_vertex_core_separation_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {eps : ℝ}
-- given
  (heps : 0 < eps ∧ eps < 1 / 2) :
-- imply
  ∃ r : NNReal, 0 < r ∧ ∀ v i : Fin n, ∀ y ∈ polygon.closedEdgeCore eps i, (r : ℝ) < dist (polygon.vertex v) y := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_uniform_vertex_core_separation polygon heps

/--
[KWFiniteSimplePolygon.vertexBall_disjoint_closedEdgeCoreTube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardVertexCoreSeparation.lean)
-/
@[path]
private lemma vertexBall_disjoint_closedEdgeCoreTube_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {eps : ℝ}
  {r : NNReal}
  {v i : Fin n}
-- given
  (hsep : ∀ v i : Fin n, ∀ y ∈ polygon.closedEdgeCore eps i, (r : ℝ) < dist (polygon.vertex v) y) :
-- imply
  Disjoint (Metric.ball (polygon.vertex v) ((r : ℝ) / 2)) (polygon.closedEdgeCoreTube eps (r / 2) i) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.vertexBall_disjoint_closedEdgeCoreTube polygon hsep v i

/--
[KWFiniteSimplePolygon.exists_pairwise_vertexBall_coreTube_separation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardVertexCoreSeparation.lean)
-/
@[path]
private lemma exists_pairwise_vertexBall_coreTube_separation_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {eps : ℝ}
-- given
  (heps : 0 < eps ∧ eps < 1 / 2) :
-- imply
  ∃ r : NNReal, 0 < r ∧ ∀ v i : Fin n, Disjoint (Metric.ball (polygon.vertex v) (r : ℝ)) (polygon.closedEdgeCoreTube eps r i) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_pairwise_vertexBall_coreTube_separation polygon heps


-- created on 2026-10-23
