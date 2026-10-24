import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.KacWardRectilinearSeparation
open StatMech StatMech.FrontierA


/--
[KWEdgesNonincident.symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearSeparation.lean)
-/
@[path]
private lemma symm_eq
  {n : ℕ}
  [NeZero n]
  {i j : Fin n}
-- given
  (h : KWEdgesNonincident i j) :
-- imply
  KWEdgesNonincident j i := by
-- proof
  apply StatMech.FrontierA.KWEdgesNonincident.symm h

/--
[KWEdgesNonincident.succ_ne_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearSeparation.lean)
-/
@[path]
private lemma succ_ne_succ_eq
  {n : ℕ}
  [NeZero n]
  {i j : Fin n}
-- given
  (h : KWEdgesNonincident i j) :
-- imply
  i + 1 ≠ j + 1 := by
-- proof
  apply StatMech.FrontierA.KWEdgesNonincident.succ_ne_succ h

/--
[KWFiniteSimplePolygon.closedEdge_isCompact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearSeparation.lean)
-/
@[path]
private lemma closedEdge_isCompact_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n} :
-- imply
  IsCompact (polygon.closedEdge i) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.closedEdge_isCompact polygon i

/--
[KWFiniteSimplePolygon.closedEdge_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearSeparation.lean)
-/
@[path]
private lemma closedEdge_isClosed_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n} :
-- imply
  IsClosed (polygon.closedEdge i) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.closedEdge_isClosed polygon i

/--
[KWFiniteSimplePolygon.closedEdge_disjoint_of_nonincident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearSeparation.lean)
-/
@[path]
private lemma closedEdge_disjoint_of_nonincident_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i j : Fin n}
-- given
  (hij : KWEdgesNonincident i j) :
-- imply
  Disjoint (polygon.closedEdge i) (polygon.closedEdge j) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.closedEdge_disjoint_of_nonincident polygon hij

/--
[KWFiniteSimplePolygon.exists_uniform_vertex_separation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearSeparation.lean)
-/
@[path]
private lemma exists_uniform_vertex_separation_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n} :
-- imply
  ∃ r : ℝ≥0, 0 < r ∧ ∀ i j : Fin n, i ≠ j → (r : ℝ) < dist (polygon.vertex i) (polygon.vertex j) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_uniform_vertex_separation polygon

/--
[KWFiniteSimplePolygon.exists_uniform_nonincident_edge_separation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearSeparation.lean)
-/
@[path]
private lemma exists_uniform_nonincident_edge_separation_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n} :
-- imply
  ∃ r : ℝ≥0, 0 < r ∧ ∀ i j : Fin n, KWEdgesNonincident i j → ∀ x ∈ polygon.closedEdge i, ∀ y ∈ polygon.closedEdge j, (r : ℝ≥0∞) < edist x y := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_uniform_nonincident_edge_separation polygon

/--
[KWFiniteSimplePolygon.exists_uniform_nonincident_edge_dist_separation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearSeparation.lean)
-/
@[path]
private lemma exists_uniform_nonincident_edge_dist_separation_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n} :
-- imply
  ∃ r : ℝ≥0, 0 < r ∧ ∀ i j : Fin n, KWEdgesNonincident i j → ∀ x ∈ polygon.closedEdge i, ∀ y ∈ polygon.closedEdge j, (r : ℝ) < dist x y := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_uniform_nonincident_edge_dist_separation polygon

/--
[KWFiniteSimplePolygon.closedEdgeTube_eq_add_ball](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearSeparation.lean)
-/
@[path]
private lemma closedEdgeTube_eq_add_ball_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (r : ℝ≥0) :
-- imply
  polygon.closedEdgeTube r i = polygon.closedEdge i + Metric.ball (0 : ℂ) (r : ℝ) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.closedEdgeTube_eq_add_ball polygon r i

/--
[KWFiniteSimplePolygon.closedEdgeTube_convex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearSeparation.lean)
-/
@[path]
private lemma closedEdgeTube_convex_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (r : ℝ≥0) :
-- imply
  Convex ℝ (polygon.closedEdgeTube r i) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.closedEdgeTube_convex polygon r i

/--
[KWFiniteSimplePolygon.closedEdge_subset_closedEdgeTube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearSeparation.lean)
-/
@[path]
private lemma closedEdge_subset_closedEdgeTube_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {r : ℝ≥0}
  {i : Fin n}
-- given
  (hr : 0 < r) :
-- imply
  polygon.closedEdge i ⊆ polygon.closedEdgeTube r i := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.closedEdge_subset_closedEdgeTube polygon hr i

/--
[KWFiniteSimplePolygon.closedEdgeTube_disjoint_of_nonincident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearSeparation.lean)
-/
@[path]
private lemma closedEdgeTube_disjoint_of_nonincident_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {r : ℝ≥0}
  {i j : Fin n}
-- given
  (hsep : ∀ i j : Fin n, KWEdgesNonincident i j → ∀ x ∈ polygon.closedEdge i, ∀ y ∈ polygon.closedEdge j, (r : ℝ) < dist x y)
  (hij : KWEdgesNonincident i j) :
-- imply
  Disjoint (polygon.closedEdgeTube (r / 2) i) (polygon.closedEdgeTube (r / 2) j) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.closedEdgeTube_disjoint_of_nonincident polygon hsep hij

/--
[KWFiniteSimplePolygon.exists_pairwise_disjoint_nonincident_edgeTubes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearSeparation.lean)
-/
@[path]
private lemma exists_pairwise_disjoint_nonincident_edgeTubes_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n} :
-- imply
  ∃ r : ℝ≥0, 0 < r ∧ ∀ i j : Fin n, KWEdgesNonincident i j → Disjoint (polygon.closedEdgeTube (r / 2) i) (polygon.closedEdgeTube (r / 2) j) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_pairwise_disjoint_nonincident_edgeTubes polygon


-- created on 2026-10-23
