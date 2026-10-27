import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveIdealPlacement
open StatMech StatMech.FrontierA


/--
[KWAdaptivePatchedData.retainedBase_mem_closedEdgeCore](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealPlacement.lean)
-/
@[path]
private lemma retainedBase_mem_closedEdgeCore_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {eps : ℝ}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hepsBeta : eps ≤ patch.beta)
  (hepsAlpha : ∀ i, eps ≤ patch.alpha i) :
-- imply
  patch.data.base i q.succ.castSucc.castSucc ∈ polygon.closedEdgeCore eps i := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.retainedBase_mem_closedEdgeCore patch hepsBeta hepsAlpha i q

/--
[KWAdaptivePatchedData.retainedNextBase_mem_closedEdgeCore](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealPlacement.lean)
-/
@[path]
private lemma retainedNextBase_mem_closedEdgeCore_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {eps : ℝ}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hepsBeta : eps ≤ patch.beta)
  (hepsAlpha : ∀ i, eps ≤ patch.alpha i) :
-- imply
  patch.data.base i q.succ.castSucc.succ ∈ polygon.closedEdgeCore eps i := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.retainedNextBase_mem_closedEdgeCore patch hepsBeta hepsAlpha i q

/--
[KWAdaptivePatchedData.idealMiddleCorner_mem_closedEdgeCore](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealPlacement.lean)
-/
@[path]
private lemma idealMiddleCorner_mem_closedEdgeCore_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {eps : ℝ}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hepsBeta : eps ≤ patch.beta)
  (hepsAlpha : ∀ i, eps ≤ patch.alpha i) :
-- imply
  patch.idealMiddleCorner i q ∈ polygon.closedEdgeCore eps i := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealMiddleCorner_mem_closedEdgeCore patch hepsBeta hepsAlpha i q

/--
[KWAdaptivePatchedData.idealRawClosedEdge_even_subset_core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealPlacement.lean)
-/
@[path]
private lemma idealRawClosedEdge_even_subset_core_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {eps : ℝ}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hepsBeta : eps ≤ patch.beta)
  (hepsAlpha : ∀ i, eps ≤ patch.alpha i) :
-- imply
  kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i q.castSucc) ⊆ polygon.closedEdgeCore eps i := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealRawClosedEdge_even_subset_core patch hepsBeta hepsAlpha i q

/--
[KWAdaptivePatchedData.idealRawClosedEdge_odd_subset_core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealPlacement.lean)
-/
@[path]
private lemma idealRawClosedEdge_odd_subset_core_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {eps : ℝ}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hepsBeta : eps ≤ patch.beta)
  (hepsAlpha : ∀ i, eps ≤ patch.alpha i) :
-- imply
  kwRawClosedEdge patch.idealVertex (kwStairOddIndex i q.castSucc) ⊆ polygon.closedEdgeCore eps i := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealRawClosedEdge_odd_subset_core patch hepsBeta hepsAlpha i q

/--
[KWAdaptivePatchedData.idealConnectorClosedEdges_subset_ball](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealPlacement.lean)
-/
@[path]
private lemma idealConnectorClosedEdges_subset_ball_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {r : ℝ}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hr : 0 < r)
  (ha : ‖patch.alpha (i + 1) * (-polygon.edgeVector i)‖ < r / 2)
  (hb : ‖patch.beta * polygon.edgeVector (i + 1)‖ < r / 2) :
-- imply
  kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i (Fin.last M)) ⊆ Metric.ball (polygon.vertex (i + 1)) r ∧ kwRawClosedEdge patch.idealVertex (kwStairOddIndex i (Fin.last M)) ⊆ Metric.ball (polygon.vertex (i + 1)) r := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealConnectorClosedEdges_subset_ball patch i hr ha hb

/--
[KWSmallAdaptiveConnectorScales.idealConnectorClosedEdges_subset_vertexBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealPlacement.lean)
-/
@[path]
private lemma idealConnectorClosedEdges_subset_vertexBall_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {neighborhood : KWVertexNeighborhoodData polygon}
  {scales : KWSmallAdaptiveConnectorScales polygon neighborhood.scale}
  {i : Fin n}
-- given
  (hM : 2 ≤ M) :
-- imply
  let patch := scales.toPatchedData hM kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i (Fin.last M)) ⊆ neighborhood.vertexBall (i + 1) ∧ kwRawClosedEdge patch.idealVertex (kwStairOddIndex i (Fin.last M)) ⊆ neighborhood.vertexBall (i + 1) := by
-- proof
  apply StatMech.FrontierA.KWSmallAdaptiveConnectorScales.idealConnectorClosedEdges_subset_vertexBall neighborhood scales hM i


-- created on 2026-10-23
