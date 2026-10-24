import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveIdealGlobalSeparation
open StatMech StatMech.FrontierA


/--
[KWAdaptivePatchedData.idealMiddle_subset_closedEdgeTube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealGlobalSeparation.lean)
-/
@[path]
private lemma idealMiddle_subset_closedEdgeTube_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {eps : ℝ}
  {neighborhood : KWVertexNeighborhoodData polygon}
  {i : Fin n}
  {q : Fin M}
  {even : Bool}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (heps : 0 < eps ∧ eps < 1 / 2)
  (hepsBeta : eps ≤ patch.beta)
  (hepsAlpha : ∀ i, eps ≤ patch.alpha i) :
-- imply
  patch.idealMiddleClosedEdge i q even ⊆ neighborhood.edgeTube i := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealMiddle_subset_closedEdgeTube patch heps hepsBeta hepsAlpha neighborhood i q even

/--
[KWSmallAdaptiveConnectorScales.idealConnector_subset_vertexBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealGlobalSeparation.lean)
-/
@[path]
private lemma idealConnector_subset_vertexBall_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {neighborhood : KWVertexNeighborhoodData polygon}
  {scales : KWSmallAdaptiveConnectorScales polygon neighborhood.scale}
  {i : Fin n}
  {even : Bool}
-- given
  (hM : 2 ≤ M) :
-- imply
  let patch := scales.toPatchedData hM kwRawClosedEdge patch.idealVertex (kwAdaptiveIdealIndex i (Fin.last M) even) ⊆ neighborhood.vertexBall (i + 1) := by
-- proof
  apply StatMech.FrontierA.KWSmallAdaptiveConnectorScales.idealConnector_subset_vertexBall neighborhood scales hM i even

/--
[KWSmallAdaptiveConnectorScales.ideal_nonincident_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealGlobalSeparation.lean)
-/
@[path]
private lemma ideal_nonincident_disjoint_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {neighborhood : KWVertexNeighborhoodData polygon}
  {scales : KWSmallAdaptiveConnectorScales polygon neighborhood.scale}
-- given
  (hM : 2 ≤ M)
  (hcross : ∀ i : Fin n, kwComplexCross (polygon.edgeVector i) (polygon.edgeVector (i + 1)) ≠ 0)
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0) :
-- imply
  let patch := scales.toPatchedData hM ∀ a b : Fin (n * (2 * (M + 1))), KWEdgesNonincident a b → Disjoint (kwRawClosedEdge patch.idealVertex a) (kwRawClosedEdge patch.idealVertex b) := by
-- proof
  apply StatMech.FrontierA.KWSmallAdaptiveConnectorScales.ideal_nonincident_disjoint neighborhood scales hM hcross hcoords


-- created on 2026-10-23
