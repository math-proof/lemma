import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardCoreTubes
open StatMech StatMech.FrontierA


/--
[KWFiniteSimplePolygon.closedEdgeCore_convex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCoreTubes.lean)
-/
@[path]
private lemma closedEdgeCore_convex_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {eps : ℝ}
  {i : Fin n} :
-- imply
  Convex ℝ (polygon.closedEdgeCore eps i) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.closedEdgeCore_convex polygon eps i

/--
[KWFiniteSimplePolygon.closedEdgeCoreTube_eq_add_ball](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCoreTubes.lean)
-/
@[path]
private lemma closedEdgeCoreTube_eq_add_ball_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {eps : ℝ}
  {i : Fin n}
-- given
  (r : ℝ≥0) :
-- imply
  polygon.closedEdgeCoreTube eps r i = polygon.closedEdgeCore eps i + Metric.ball (0 : ℂ) (r : ℝ) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.closedEdgeCoreTube_eq_add_ball polygon eps r i

/--
[KWFiniteSimplePolygon.closedEdgeCoreTube_convex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCoreTubes.lean)
-/
@[path]
private lemma closedEdgeCoreTube_convex_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {eps : ℝ}
  {i : Fin n}
-- given
  (r : ℝ≥0) :
-- imply
  Convex ℝ (polygon.closedEdgeCoreTube eps r i) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.closedEdgeCoreTube_convex polygon eps r i

/--
[nnreal_lt_edist_iff_lt_dist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCoreTubes.lean)
-/
@[path]
private lemma nnreal_lt_edist_iff_lt_dist_eq
  {r : ℝ≥0}
  {x y : ℂ} :
-- imply
  (r : ℝ≥0∞) < edist x y ↔ (r : ℝ) < dist x y := by
-- proof
  apply StatMech.FrontierA.nnreal_lt_edist_iff_lt_dist

/--
[KWFiniteSimplePolygon.closedEdgeCoreTube_disjoint_of_separation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCoreTubes.lean)
-/
@[path]
private lemma closedEdgeCoreTube_disjoint_of_separation_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {eps : ℝ}
  {r : ℝ≥0}
  {i j : Fin n}
-- given
  (hsep : ∀ i j : Fin n, i ≠ j → ∀ x ∈ polygon.closedEdgeCore eps i, ∀ y ∈ polygon.closedEdgeCore eps j, (r : ℝ≥0∞) < edist x y)
  (hij : i ≠ j) :
-- imply
  Disjoint (polygon.closedEdgeCoreTube eps (r / 2) i) (polygon.closedEdgeCoreTube eps (r / 2) j) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.closedEdgeCoreTube_disjoint_of_separation polygon hsep hij

/--
[KWFiniteSimplePolygon.exists_pairwise_disjoint_closedEdgeCoreTubes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCoreTubes.lean)
-/
@[path]
private lemma exists_pairwise_disjoint_closedEdgeCoreTubes_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {eps : ℝ}
-- given
  (heps : 0 < eps ∧ eps < 1 / 2) :
-- imply
  ∃ r : ℝ≥0, 0 < r ∧ ∀ i j : Fin n, i ≠ j → Disjoint (polygon.closedEdgeCoreTube eps r i) (polygon.closedEdgeCoreTube eps r j) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_pairwise_disjoint_closedEdgeCoreTubes polygon heps


-- created on 2026-10-23
