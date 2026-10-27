import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveActualGlobalSeparation
open StatMech StatMech.FrontierA


/--
[KWAdaptivePatchedData.middle_subset_edgeTube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualGlobalSeparation.lean)
-/
@[path]
private lemma middle_subset_edgeTube_eq
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
  (hepsAlpha : ∀ i, eps ≤ patch.alpha i)
  (r : ℝ≥0)
  (hr : 0 < r)
  (hfine : KWEndpointInteriorMeshWithin patch.data r)
  (hrScale : r ≤ neighborhood.scale / 2) :
-- imply
  patch.middleClosedEdge i q even ⊆ neighborhood.edgeTube i := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.middle_subset_edgeTube patch heps hepsBeta hepsAlpha neighborhood r hr hfine hrScale i q even

/--
[KWSmallAdaptiveConnectorScales.actualConnector_subset_vertexBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualGlobalSeparation.lean)
-/
@[path]
private lemma actualConnector_subset_vertexBall_eq
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
  let patch := scales.toPatchedData hM kwRawClosedEdge patch.vertex (kwAdaptiveIdealIndex i (Fin.last M) even) ⊆ neighborhood.vertexBall (i + 1) := by
-- proof
  apply StatMech.FrontierA.KWSmallAdaptiveConnectorScales.actualConnector_subset_vertexBall neighborhood scales hM i even

/--
[KWSmallAdaptiveConnectorScales.actual_nonincident_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualGlobalSeparation.lean)
-/
@[path]
private lemma actual_nonincident_disjoint_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {neighborhood : KWVertexNeighborhoodData polygon}
  {scales : KWSmallAdaptiveConnectorScales polygon neighborhood.scale}
  {eps : ℝ}
-- given
  (hM : 2 ≤ M)
  (heps : 0 < eps ∧ eps < 1 / 2)
  (hepsBeta : eps ≤ scales.beta)
  (hepsAlpha : ∀ i, eps ≤ scales.alpha i)
  (r sep : ℝ≥0)
  (hr : 0 < r)
  (hfine : KWEndpointInteriorMeshWithin (scales.toPatchedData hM).data r)
  (hrScale : r ≤ neighborhood.scale / 2)
  (hcore : ∀ i j : Fin n, i ≠ j → Disjoint (polygon.closedEdgeCoreTube eps r i) (polygon.closedEdgeCoreTube eps r j))
  (hcoords : ∀ j : Fin n, (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
  (hsep : let patch := scales.toPatchedData hM ∀ i : Fin n, ∀ first : Bool, ∀ x ∈ (if first then kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i (Fin.last M)) else kwRawClosedEdge patch.idealVertex (kwStairOddIndex i (Fin.last M))), ∀ y ∈ (if first then patch.outgoingParameterCarrier (i + 1) else patch.incomingParameterCarrier i), (sep : ℝ) < dist x y)
  (hsmall : 4 * (r : ℝ) < sep) :
-- imply
  let patch := scales.toPatchedData hM ∀ a b : Fin (n * (2 * (M + 1))), KWEdgesNonincident a b → Disjoint (kwRawClosedEdge patch.vertex a) (kwRawClosedEdge patch.vertex b) := by
-- proof
  apply StatMech.FrontierA.KWSmallAdaptiveConnectorScales.actual_nonincident_disjoint neighborhood scales hM heps hepsBeta hepsAlpha r sep hr hfine hrScale hcore hcoords hsep hsmall

/--
[KWSmallAdaptiveConnectorScales.actualRawSimpleData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualGlobalSeparation.lean)
-/
@[path]
private lemma actualRawSimpleData_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {neighborhood : KWVertexNeighborhoodData polygon}
  {scales : KWSmallAdaptiveConnectorScales polygon neighborhood.scale}
  {eps : ℝ}
-- given
  (hM : 2 ≤ M)
  (heps : 0 < eps ∧ eps < 1 / 2)
  (hepsBeta : eps ≤ scales.beta)
  (hepsAlpha : ∀ i, eps ≤ scales.alpha i)
  (r sep : ℝ≥0)
  (hr : 0 < r)
  (hfine : KWEndpointInteriorMeshWithin (scales.toPatchedData hM).data r)
  (hrScale : r ≤ neighborhood.scale / 2)
  (hcore : ∀ i j : Fin n, i ≠ j → Disjoint (polygon.closedEdgeCoreTube eps r i) (polygon.closedEdgeCoreTube eps r j))
  (hcoords : ∀ j : Fin n, (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
  (hsep : let patch := scales.toPatchedData hM ∀ i : Fin n, ∀ first : Bool, ∀ x ∈ (if first then kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i (Fin.last M)) else kwRawClosedEdge patch.idealVertex (kwStairOddIndex i (Fin.last M))), ∀ y ∈ (if first then patch.outgoingParameterCarrier (i + 1) else patch.incomingParameterCarrier i), (sep : ℝ) < dist x y)
  (hsmall : 4 * (r : ℝ) < sep) :
-- imply
  let patch := scales.toPatchedData hM KWRawNonbacktrackingSimpleData patch.vertex := by
-- proof
  apply StatMech.FrontierA.KWSmallAdaptiveConnectorScales.actualRawSimpleData neighborhood scales hM heps hepsBeta hepsAlpha r sep hr hfine hrScale hcore hcoords hsep hsmall

/--
[KWSmallAdaptiveConnectorScales.exists_actualSimplePolygon_eq_patch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualGlobalSeparation.lean)
-/
@[path]
private lemma exists_actualSimplePolygon_eq_patch_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {neighborhood : KWVertexNeighborhoodData polygon}
  {scales : KWSmallAdaptiveConnectorScales polygon neighborhood.scale}
-- given
  (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j) (polygon.edgeVector (j + 1)) ≠ 0)
  (hcoords : ∀ j : Fin n, (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0) :
-- imply
  ∃ M : ℕ, ∃ inst : NeZero M, ∃ hM : 2 ≤ M, letI : NeZero M := inst ∃ actual : KWFiniteSimplePolygon (n * (2 * (M + 1))), actual.vertex = (scales.toPatchedData hM).vertex := by
-- proof
  apply StatMech.FrontierA.KWSmallAdaptiveConnectorScales.exists_actualSimplePolygon_eq_patch neighborhood scales hcross hcoords

/--
[KWSmallAdaptiveConnectorScales.exists_actualSimplePolygon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualGlobalSeparation.lean)
-/
@[path]
private lemma exists_actualSimplePolygon_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {neighborhood : KWVertexNeighborhoodData polygon}
  {scales : KWSmallAdaptiveConnectorScales polygon neighborhood.scale}
-- given
  (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j) (polygon.edgeVector (j + 1)) ≠ 0)
  (hcoords : ∀ j : Fin n, (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0) :
-- imply
  ∃ M : ℕ, ∃ inst : NeZero M, ∃ hM : 2 ≤ M, letI : NeZero M := inst Nonempty (KWFiniteSimplePolygon (n * (2 * (M + 1)))) := by
-- proof
  apply StatMech.FrontierA.KWSmallAdaptiveConnectorScales.exists_actualSimplePolygon neighborhood scales hcross hcoords


-- created on 2026-10-23
