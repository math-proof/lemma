import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdjacentCoreSeparation
open StatMech StatMech.FrontierA


/--
[KWFiniteSimplePolygon.closedEdgeCore_isCompact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdjacentCoreSeparation.lean)
-/
@[path]
private lemma closedEdgeCore_isCompact_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {eps : ℝ}
  {i : Fin n} :
-- imply
  IsCompact (polygon.closedEdgeCore eps i) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.closedEdgeCore_isCompact polygon eps i

/--
[KWFiniteSimplePolygon.closedEdgeCore_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdjacentCoreSeparation.lean)
-/
@[path]
private lemma closedEdgeCore_isClosed_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {eps : ℝ}
  {i : Fin n} :
-- imply
  IsClosed (polygon.closedEdgeCore eps i) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.closedEdgeCore_isClosed polygon eps i

/--
[KWFiniteSimplePolygon.closedEdgeCore_subset_edgeInterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdjacentCoreSeparation.lean)
-/
@[path]
private lemma closedEdgeCore_subset_edgeInterior_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {eps : ℝ}
  {i : Fin n}
-- given
  (heps : 0 < eps ∧ eps < 1 / 2) :
-- imply
  polygon.closedEdgeCore eps i ⊆ {z : ℂ | Sbtw ℝ (polygon.vertex i) z (polygon.vertex (i + 1))} := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.closedEdgeCore_subset_edgeInterior polygon heps i

/--
[KWFiniteSimplePolygon.closedEdgeCore_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdjacentCoreSeparation.lean)
-/
@[path]
private lemma closedEdgeCore_disjoint_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {eps : ℝ}
  {i j : Fin n}
-- given
  (heps : 0 < eps ∧ eps < 1 / 2)
  (hij : i ≠ j) :
-- imply
  Disjoint (polygon.closedEdgeCore eps i) (polygon.closedEdgeCore eps j) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.closedEdgeCore_disjoint polygon heps hij

/--
[KWFiniteSimplePolygon.exists_closedEdgeCore_separation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdjacentCoreSeparation.lean)
-/
@[path]
private lemma exists_closedEdgeCore_separation_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {eps : ℝ}
  {i j : Fin n}
-- given
  (heps : 0 < eps ∧ eps < 1 / 2)
  (hij : i ≠ j) :
-- imply
  ∃ r : ℝ≥0, 0 < r ∧ ∀ x ∈ polygon.closedEdgeCore eps i, ∀ y ∈ polygon.closedEdgeCore eps j, (r : ℝ≥0∞) < edist x y := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_closedEdgeCore_separation polygon heps hij

/--
[KWFiniteSimplePolygon.exists_uniform_closedEdgeCore_separation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdjacentCoreSeparation.lean)
-/
@[path]
private lemma exists_uniform_closedEdgeCore_separation_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {eps : ℝ}
-- given
  (heps : 0 < eps ∧ eps < 1 / 2) :
-- imply
  ∃ r : ℝ≥0, 0 < r ∧ ∀ i j : Fin n, i ≠ j → ∀ x ∈ polygon.closedEdgeCore eps i, ∀ y ∈ polygon.closedEdgeCore eps j, (r : ℝ≥0∞) < edist x y := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_uniform_closedEdgeCore_separation polygon heps


-- created on 2026-10-23
