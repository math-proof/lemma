import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptivePatchedPlacement
open StatMech StatMech.FrontierA


/--
[norm_kwHVConnectorCorner_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedPlacement.lean)
-/
@[path]
private lemma norm_kwHVConnectorCorner_le_eq
  {a b : ℂ} :
-- imply
  ‖kwHVConnectorCorner a b‖ ≤ ‖a‖ + ‖b‖ := by
-- proof
  apply StatMech.FrontierA.norm_kwHVConnectorCorner_le a b

/--
[norm_kwVHConnectorCorner_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedPlacement.lean)
-/
@[path]
private lemma norm_kwVHConnectorCorner_le_eq
  {a b : ℂ} :
-- imply
  ‖kwVHConnectorCorner a b‖ ≤ ‖a‖ + ‖b‖ := by
-- proof
  apply StatMech.FrontierA.norm_kwVHConnectorCorner_le a b

/--
[KWAdaptiveConnectorData.norm_corner_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedPlacement.lean)
-/
@[path]
private lemma norm_corner_le_eq
  {a b : ℂ}
  {connector : KWAdaptiveConnectorData a b} :
-- imply
  ‖connector.corner‖ ≤ ‖a‖ + ‖b‖ := by
-- proof
  apply StatMech.FrontierA.KWAdaptiveConnectorData.norm_corner_le connector

/--
[KWAdaptivePatchedData.parameter_mem_core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedPlacement.lean)
-/
@[path]
private lemma parameter_mem_core_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {eps : ℝ}
  {i : Fin n}
  {k : Fin (M + 2)}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hepsBeta : eps ≤ patch.beta)
  (hepsAlpha : ∀ i, eps ≤ patch.alpha i)
  (hk : k ≠ 0) :
-- imply
  patch.data.parameter i k.castSucc ∈ Icc eps (1 - eps) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.parameter_mem_core patch hepsBeta hepsAlpha i k hk

/--
[KWAdaptivePatchedData.middleCorner_mem_coreTube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedPlacement.lean)
-/
@[path]
private lemma middleCorner_mem_coreTube_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {eps : ℝ}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (r : ℝ≥0)
  (hr : 0 < r)
  (hmesh : KWEndpointInteriorMeshWithin patch.data r)
  (hepsBeta : eps ≤ patch.beta)
  (hepsAlpha : ∀ i, eps ≤ patch.alpha i) :
-- imply
  patch.middleCorner i q ∈ polygon.closedEdgeCoreTube eps r i := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.middleCorner_mem_coreTube patch r hr hmesh hepsBeta hepsAlpha i q

/--
[KWAdaptivePatchedData.pathBase_mem_coreTube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedPlacement.lean)
-/
@[path]
private lemma pathBase_mem_coreTube_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {eps : ℝ}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (r : ℝ≥0)
  (hr : 0 < r)
  (hepsBeta : eps ≤ patch.beta)
  (hepsAlpha : ∀ i, eps ≤ patch.alpha i) :
-- imply
  patch.pathBase i q.castSucc ∈ polygon.closedEdgeCoreTube eps r i := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.pathBase_mem_coreTube patch r hr hepsBeta hepsAlpha i q

/--
[KWAdaptivePatchedData.pathBase_succ_eq_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedPlacement.lean)
-/
@[path]
private lemma pathBase_succ_eq_base_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  patch.pathBase i q.succ = patch.data.base i q.succ.succ.castSucc := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.pathBase_succ_eq_base patch i q

/--
[KWAdaptivePatchedData.pathBase_succ_mem_coreTube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedPlacement.lean)
-/
@[path]
private lemma pathBase_succ_mem_coreTube_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {eps : ℝ}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (r : ℝ≥0)
  (hr : 0 < r)
  (hepsBeta : eps ≤ patch.beta)
  (hepsAlpha : ∀ i, eps ≤ patch.alpha i) :
-- imply
  patch.pathBase i q.succ ∈ polygon.closedEdgeCoreTube eps r i := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.pathBase_succ_mem_coreTube patch r hr hepsBeta hepsAlpha i q

/--
[KWAdaptivePatchedData.rawClosedEdge_even_castSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedPlacement.lean)
-/
@[path]
private lemma rawClosedEdge_even_castSucc_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  kwRawClosedEdge patch.vertex (kwStairEvenIndex i q.castSucc) = segment ℝ (patch.pathBase i q.castSucc) (patch.middleCorner i q) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.rawClosedEdge_even_castSucc patch i q

/--
[KWAdaptivePatchedData.rawClosedEdge_odd_castSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedPlacement.lean)
-/
@[path]
private lemma rawClosedEdge_odd_castSucc_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  kwRawClosedEdge patch.vertex (kwStairOddIndex i q.castSucc) = segment ℝ (patch.middleCorner i q) (patch.pathBase i q.succ) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.rawClosedEdge_odd_castSucc patch i q

/--
[KWAdaptivePatchedData.middle_rawClosedEdges_subset_coreTube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedPlacement.lean)
-/
@[path]
private lemma middle_rawClosedEdges_subset_coreTube_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {eps : ℝ}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (r : ℝ≥0)
  (hr : 0 < r)
  (hmesh : KWEndpointInteriorMeshWithin patch.data r)
  (hepsBeta : eps ≤ patch.beta)
  (hepsAlpha : ∀ i, eps ≤ patch.alpha i) :
-- imply
  kwRawClosedEdge patch.vertex (kwStairEvenIndex i q.castSucc) ⊆ polygon.closedEdgeCoreTube eps r i ∧ kwRawClosedEdge patch.vertex (kwStairOddIndex i q.castSucc) ⊆ polygon.closedEdgeCoreTube eps r i := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.middle_rawClosedEdges_subset_coreTube patch r hr hmesh hepsBeta hepsAlpha i q

/--
[KWAdaptivePatchedData.connectorCorner_mem_ball](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedPlacement.lean)
-/
@[path]
private lemma connectorCorner_mem_ball_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {R : ℝ}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hR : 0 < R)
  (hin : patch.alpha i * ‖polygon.edgeVector (i - 1)‖ < R / 2)
  (hout : patch.beta * ‖polygon.edgeVector i‖ < R / 2) :
-- imply
  patch.connectorCorner i ∈ Metric.ball (polygon.vertex i) R := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.connectorCorner_mem_ball patch i R hR hin hout

/--
[KWAdaptivePatchedData.incomingPort_mem_ball](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedPlacement.lean)
-/
@[path]
private lemma incomingPort_mem_ball_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {R : ℝ}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hin : patch.alpha (i + 1) * ‖polygon.edgeVector i‖ < R) :
-- imply
  patch.incomingPort i ∈ Metric.ball (polygon.vertex (i + 1)) R := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.incomingPort_mem_ball patch i R hin

/--
[KWAdaptivePatchedData.outgoingPort_mem_ball](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedPlacement.lean)
-/
@[path]
private lemma outgoingPort_mem_ball_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {R : ℝ}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hout : patch.beta * ‖polygon.edgeVector i‖ < R) :
-- imply
  patch.outgoingPort i ∈ Metric.ball (polygon.vertex i) R := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.outgoingPort_mem_ball patch i R hout

/--
[KWAdaptivePatchedData.connector_rawClosedEdges_subset_ball](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedPlacement.lean)
-/
@[path]
private lemma connector_rawClosedEdges_subset_ball_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {R : ℝ}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hR : 0 < R)
  (hin : patch.alpha (i + 1) * ‖polygon.edgeVector i‖ < R / 2)
  (hout : patch.beta * ‖polygon.edgeVector (i + 1)‖ < R / 2) :
-- imply
  kwRawClosedEdge patch.vertex (kwStairEvenIndex i (Fin.last M)) ⊆ Metric.ball (polygon.vertex (i + 1)) R ∧ kwRawClosedEdge patch.vertex (kwStairOddIndex i (Fin.last M)) ⊆ Metric.ball (polygon.vertex (i + 1)) R := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.connector_rawClosedEdges_subset_ball patch i R hR hin hout


-- created on 2026-10-23
