import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveActualIncidentSeparation.Part2
open StatMech StatMech.FrontierA


/--
[KWAdaptivePatchedData.connectorFirstClosedEdge_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualIncidentSeparation.lean)
-/
@[path]
private lemma connectorFirstClosedEdge_eq_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  kwRawClosedEdge patch.vertex (kwStairEvenIndex i (Fin.last M)) = segment ℝ (patch.incomingPort i) (patch.connectorCorner (i + 1)) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.connectorFirstClosedEdge_eq patch i

/--
[KWAdaptivePatchedData.connectorSecondClosedEdge_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualIncidentSeparation.lean)
-/
@[path]
private lemma connectorSecondClosedEdge_eq_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  kwRawClosedEdge patch.vertex (kwStairOddIndex i (Fin.last M)) = segment ℝ (patch.connectorCorner (i + 1)) (patch.outgoingPort (i + 1)) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.connectorSecondClosedEdge_eq patch i

/--
[KWAdaptivePatchedData.firstConnector_point_re_of_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualIncidentSeparation.lean)
-/
@[path]
private lemma firstConnector_point_re_of_vertical_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {z : ℂ}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hv : patch.connectorUsesVerticalFirst (i + 1))
  (hz : z ∈ kwRawClosedEdge patch.vertex (kwStairEvenIndex i (Fin.last M))) :
-- imply
  z.re = (patch.incomingPort i).re := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.firstConnector_point_re_of_vertical patch hv hz

/--
[KWAdaptivePatchedData.firstConnector_point_im_of_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualIncidentSeparation.lean)
-/
@[path]
private lemma firstConnector_point_im_of_horizontal_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {z : ℂ}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hv : ¬patch.connectorUsesVerticalFirst (i + 1))
  (hz : z ∈ kwRawClosedEdge patch.vertex (kwStairEvenIndex i (Fin.last M))) :
-- imply
  z.im = (patch.incomingPort i).im := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.firstConnector_point_im_of_horizontal patch hv hz

/--
[KWAdaptivePatchedData.secondConnector_point_im_of_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualIncidentSeparation.lean)
-/
@[path]
private lemma secondConnector_point_im_of_vertical_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {z : ℂ}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hv : patch.connectorUsesVerticalFirst (i + 1))
  (hz : z ∈ kwRawClosedEdge patch.vertex (kwStairOddIndex i (Fin.last M))) :
-- imply
  z.im = (patch.outgoingPort (i + 1)).im := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.secondConnector_point_im_of_vertical patch hv hz

/--
[KWAdaptivePatchedData.secondConnector_point_re_of_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualIncidentSeparation.lean)
-/
@[path]
private lemma secondConnector_point_re_of_horizontal_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {z : ℂ}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hv : ¬patch.connectorUsesVerticalFirst (i + 1))
  (hz : z ∈ kwRawClosedEdge patch.vertex (kwStairOddIndex i (Fin.last M))) :
-- imply
  z.re = (patch.outgoingPort (i + 1)).re := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.secondConnector_point_re_of_horizontal patch hv hz

/--
[KWAdaptivePatchedData.firstConnector_disjoint_incomingMiddle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualIncidentSeparation.lean)
-/
@[path]
private lemma firstConnector_disjoint_incomingMiddle_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
  {even : Bool}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hcoords : ∀ j : Fin n, (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
  (hnotLast : q ≠ patch.lastMiddleIndex ∨ even = true) :
-- imply
  Disjoint (kwRawClosedEdge patch.vertex (kwStairEvenIndex i (Fin.last M))) (patch.middleClosedEdge i q even) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.firstConnector_disjoint_incomingMiddle patch hcoords i q even hnotLast

/--
[KWAdaptivePatchedData.secondConnector_disjoint_outgoingMiddle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualIncidentSeparation.lean)
-/
@[path]
private lemma secondConnector_disjoint_outgoingMiddle_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
  {even : Bool}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hcoords : ∀ j : Fin n, (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
  (hnotFirst : q ≠ 0 ∨ even = false) :
-- imply
  Disjoint (kwRawClosedEdge patch.vertex (kwStairOddIndex i (Fin.last M))) (patch.middleClosedEdge (i + 1) q even) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.secondConnector_disjoint_outgoingMiddle patch hcoords i q even hnotFirst

/--
[KWAdaptivePatchedData.outgoingRetainedCarrier_subset_portTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualIncidentSeparation.lean)
-/
@[path]
private lemma outgoingRetainedCarrier_subset_portTail_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  patch.outgoingRetainedCarrier i ⊆ ({patch.outgoingPort i} ∪ kwTranslatedOpenRayTail (polygon.vertex i) (patch.beta * polygon.edgeVector i)) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.outgoingRetainedCarrier_subset_portTail patch i

/--
[KWAdaptivePatchedData.incomingRetainedCarrier_subset_portTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualIncidentSeparation.lean)
-/
@[path]
private lemma incomingRetainedCarrier_subset_portTail_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  patch.incomingRetainedCarrier i ⊆ ({patch.incomingPort i} ∪ kwTranslatedOpenRayTail (polygon.vertex (i + 1)) (patch.alpha (i + 1) * (-polygon.edgeVector i))) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.incomingRetainedCarrier_subset_portTail patch i

/--
[KWAdaptivePatchedData.firstConnector_disjoint_outgoingCarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualIncidentSeparation.lean)
-/
@[path]
private lemma firstConnector_disjoint_outgoingCarrier_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j) (polygon.edgeVector (j + 1)) ≠ 0)
  (hcoords : ∀ j : Fin n, (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0) :
-- imply
  Disjoint (kwRawClosedEdge patch.vertex (kwStairEvenIndex i (Fin.last M))) (patch.outgoingRetainedCarrier (i + 1)) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.firstConnector_disjoint_outgoingCarrier patch hcross hcoords i

/--
[KWAdaptivePatchedData.secondConnector_disjoint_incomingCarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualIncidentSeparation.lean)
-/
@[path]
private lemma secondConnector_disjoint_incomingCarrier_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j) (polygon.edgeVector (j + 1)) ≠ 0)
  (hcoords : ∀ j : Fin n, (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0) :
-- imply
  Disjoint (kwRawClosedEdge patch.vertex (kwStairOddIndex i (Fin.last M))) (patch.incomingRetainedCarrier i) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.secondConnector_disjoint_incomingCarrier patch hcross hcoords i

/--
[KWAdaptivePatchedData.exists_remoteIncident_dist_separation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualIncidentSeparation.lean)
-/
@[path]
private lemma exists_remoteIncident_dist_separation_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {first : Bool}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j) (polygon.edgeVector (j + 1)) ≠ 0)
  (hcoords : ∀ j : Fin n, (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0) :
-- imply
  ∃ r : NNReal, 0 < r ∧ ∀ x ∈ (if first then kwRawClosedEdge patch.vertex (kwStairEvenIndex i (Fin.last M)) else kwRawClosedEdge patch.vertex (kwStairOddIndex i (Fin.last M))), ∀ y ∈ (if first then patch.outgoingRetainedCarrier (i + 1) else patch.incomingRetainedCarrier i), (r : ℝ) < dist x y := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.exists_remoteIncident_dist_separation patch hcross hcoords i first


-- created on 2026-10-23
