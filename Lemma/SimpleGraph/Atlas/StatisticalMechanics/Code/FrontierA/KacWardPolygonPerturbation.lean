import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonPerturbation.Part5
open StatMech StatMech.FrontierA


/--
[dist_lineMap_le_of_endpoint_dist_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonPerturbation.lean)
-/
@[path]
private lemma dist_lineMap_le_of_endpoint_dist_le_eq
  {a b a' b' : ℂ}
  {t eps : ℝ}
-- given
  (ht : t ∈ Icc 0 1)
  (ha : dist a' a ≤ eps)
  (hb : dist b' b ≤ eps) :
-- imply
  dist (AffineMap.lineMap a' b' t) (AffineMap.lineMap a b t) ≤ eps := by
-- proof
  apply StatMech.FrontierA.dist_lineMap_le_of_endpoint_dist_le ht ha hb

/--
[exists_source_segment_point_dist_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonPerturbation.lean)
-/
@[path]
private lemma exists_source_segment_point_dist_le_eq
  {a b a' b' : ℂ}
  {eps : ℝ}
  {z : ℂ}
-- given
  (ha : dist a' a ≤ eps)
  (hb : dist b' b ≤ eps)
  (hz : z ∈ segment ℝ a' b') :
-- imply
  ∃ w ∈ segment ℝ a b, dist z w ≤ eps := by
-- proof
  apply StatMech.FrontierA.exists_source_segment_point_dist_le ha hb hz

/--
[segment_disjoint_of_perturbation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonPerturbation.lean)
-/
@[path]
private lemma segment_disjoint_of_perturbation_eq
  {a b c d a' b' c' d' : ℂ}
  {eps r : ℝ}
-- given
  (ha : dist a' a ≤ eps)
  (hb : dist b' b ≤ eps)
  (hc : dist c' c ≤ eps)
  (hd : dist d' d ≤ eps)
  (hsep : ∀ x ∈ segment ℝ a b, ∀ y ∈ segment ℝ c d, r < dist x y)
  (heps : 2 * eps < r) :
-- imply
  Disjoint (segment ℝ a' b') (segment ℝ c' d') := by
-- proof
  apply StatMech.FrontierA.segment_disjoint_of_perturbation ha hb hc hd hsep heps

/--
[KWRawSimplePolygonData.of_vertex_perturbation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonPerturbation.lean)
-/
@[path]
private lemma of_vertex_perturbation_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {vertex : Fin n → ℂ}
  {eps vertexRadius edgeRadius : ℝ}
-- given
  (hvertex : ∀ i : Fin n, dist (vertex i) (polygon.vertex i) ≤ eps)
  (hvertexSep : ∀ i j : Fin n, i ≠ j → vertexRadius < dist (polygon.vertex i) (polygon.vertex j))
  (hedgeSep : ∀ i j : Fin n, KWEdgesNonincident i j → ∀ x ∈ polygon.closedEdge i, ∀ y ∈ polygon.closedEdge j, edgeRadius < dist x y)
  (hepsVertex : 2 * eps < vertexRadius)
  (hepsEdge : 2 * eps < edgeRadius)
  (hcross : ∀ i : Fin n, kwComplexCross (kwRawEdge vertex i) (kwRawEdge vertex (i + 1)) ≠ 0) :
-- imply
  KWRawSimplePolygonData vertex := by
-- proof
  apply StatMech.FrontierA.KWRawSimplePolygonData.of_vertex_perturbation polygon vertex hvertex hvertexSep hedgeSep hepsVertex hepsEdge hcross

/--
[denseRange_kwRatComplex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonPerturbation.lean)
-/
@[path]
private lemma denseRange_kwRatComplex_eq :
-- imply
  DenseRange kwRatComplex := by
-- proof
  apply StatMech.FrontierA.denseRange_kwRatComplex

/--
[denseRange_kwRatVertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonPerturbation.lean)
-/
@[path]
private lemma denseRange_kwRatVertex_eq
  {n : ℕ} :
-- imply
  DenseRange (@kwRatVertex n) := by
-- proof
  apply StatMech.FrontierA.denseRange_kwRatVertex

/--
[exists_cross_stability_radius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonPerturbation.lean)
-/
@[path]
private lemma exists_cross_stability_radius_eq
  {n : ℕ}
  [NeZero n]
  {vertex : Fin n → ℂ}
-- given
  (hcross : ∀ i : Fin n, kwComplexCross (kwRawEdge vertex i) (kwRawEdge vertex (i + 1)) ≠ 0) :
-- imply
  ∃ eps : ℝ, 0 < eps ∧ ∀ v : Fin n → ℂ, dist v vertex < eps → ∀ i : Fin n, kwComplexCross (kwRawEdge v i) (kwRawEdge v (i + 1)) ≠ 0 := by
-- proof
  apply StatMech.FrontierA.exists_cross_stability_radius vertex hcross

/--
[KWFiniteSimplePolygon.exists_perturbationCertificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonPerturbation.lean)
-/
@[path]
private lemma exists_perturbationCertificate_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
-- given
  (hcross : ∀ i : Fin n, kwComplexCross (polygon.edgeVector i) (polygon.edgeVector (i + 1)) ≠ 0) :
-- imply
  Nonempty (KWPolygonPerturbationCertificate polygon) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_perturbationCertificate polygon hcross

/--
[KWFiniteSimplePolygon.exists_close_rational_polygon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonPerturbation.lean)
-/
@[path]
private lemma exists_close_rational_polygon_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
-- given
  (hcross : ∀ i : Fin n, kwComplexCross (polygon.edgeVector i) (polygon.edgeVector (i + 1)) ≠ 0) :
-- imply
  ∃ (q : Fin n → ℚ × ℚ) (rational : KWFiniteSimplePolygon n), rational.vertex = kwRatVertex q ∧ (∀ i : Fin n, dist (rational.vertex i) (polygon.vertex i) < 1) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_close_rational_polygon polygon hcross


-- created on 2026-10-23
