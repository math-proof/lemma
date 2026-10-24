import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveIdealApproximation
open StatMech StatMech.FrontierA


/--
[KWAdaptivePatchedData.dist_middleCorner_ideal_lt_two_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealApproximation.lean)
-/
@[path]
private lemma dist_middleCorner_ideal_lt_two_mul_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (r : ℝ≥0)
  (hfine : patch.data.MeshWithin r) :
-- imply
  dist (patch.middleCorner i q) (patch.idealMiddleCorner i q) < 2 * r := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.dist_middleCorner_ideal_lt_two_mul patch r hfine i q

/--
[KWAdaptivePatchedData.dist_vertex_idealVertex_lt_two_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealApproximation.lean)
-/
@[path]
private lemma dist_vertex_idealVertex_lt_two_mul_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (r : ℝ≥0)
  (hr : 0 < r)
  (hfine : patch.data.MeshWithin r) :
-- imply
  ∀ j : Fin (n * (2 * (M + 1))), dist (patch.vertex j) (patch.idealVertex j) < 2 * r := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.dist_vertex_idealVertex_lt_two_mul patch r hr hfine

/--
[KWAdaptivePatchedData.actual_nonincident_disjoint_of_close_to_ideal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealApproximation.lean)
-/
@[path]
private lemma actual_nonincident_disjoint_of_close_to_ideal_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {ideal : KWFiniteSimplePolygon (n * (2 * (M + 1)))}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hideal : ideal.vertex = patch.idealVertex)
  (r sep : ℝ≥0)
  (hr : 0 < r)
  (hfine : patch.data.MeshWithin r)
  (hsep : ∀ i j, KWEdgesNonincident i j → ∀ x ∈ ideal.closedEdge i, ∀ y ∈ ideal.closedEdge j, (sep : ℝ) < dist x y)
  (hsmall : 8 * (r : ℝ) < sep) :
-- imply
  ∀ i j, KWEdgesNonincident i j → Disjoint (kwRawClosedEdge patch.vertex i) (kwRawClosedEdge patch.vertex j) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.actual_nonincident_disjoint_of_close_to_ideal patch ideal hideal r sep hr hfine hsep hsmall


-- created on 2026-10-23
