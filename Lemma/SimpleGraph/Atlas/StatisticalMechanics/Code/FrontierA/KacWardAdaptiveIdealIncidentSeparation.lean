import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveIdealIncidentSeparation
open StatMech StatMech.FrontierA


/--
[KWAdaptivePatchedData.idealConnectorFirstClosedEdge_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealIncidentSeparation.lean)
-/
@[path]
private lemma idealConnectorFirstClosedEdge_eq_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i (Fin.last M)) = segment ℝ (patch.incomingPort i) (patch.connectorCorner (i + 1)) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealConnectorFirstClosedEdge_eq patch i

/--
[KWAdaptivePatchedData.idealConnectorSecondClosedEdge_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealIncidentSeparation.lean)
-/
@[path]
private lemma idealConnectorSecondClosedEdge_eq_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  kwRawClosedEdge patch.idealVertex (kwStairOddIndex i (Fin.last M)) = segment ℝ (patch.connectorCorner (i + 1)) (patch.outgoingPort (i + 1)) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealConnectorSecondClosedEdge_eq patch i

/--
[KWAdaptivePatchedData.idealConnectorClosedEdges_disjoint_incidentTails](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealIncidentSeparation.lean)
-/
@[path]
private lemma idealConnectorClosedEdges_disjoint_incidentTails_eq
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
  Disjoint (kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i (Fin.last M)) ∪ kwRawClosedEdge patch.idealVertex (kwStairOddIndex i (Fin.last M))) (kwTranslatedOpenRayTail (polygon.vertex (i + 1)) (patch.alpha (i + 1) * (-polygon.edgeVector i)) ∪ kwTranslatedOpenRayTail (polygon.vertex (i + 1)) (patch.beta * polygon.edgeVector (i + 1))) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealConnectorClosedEdges_disjoint_incidentTails patch hcross hcoords i

/--
[KWAdaptivePatchedData.idealConnectorFirstClosedEdge_disjoint_outgoingPortTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealIncidentSeparation.lean)
-/
@[path]
private lemma idealConnectorFirstClosedEdge_disjoint_outgoingPortTail_eq
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
  Disjoint (kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i (Fin.last M))) ({polygon.vertex (i + 1) + patch.beta * polygon.edgeVector (i + 1)} ∪ kwTranslatedOpenRayTail (polygon.vertex (i + 1)) (patch.beta * polygon.edgeVector (i + 1))) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealConnectorFirstClosedEdge_disjoint_outgoingPortTail patch hcross hcoords i

/--
[KWAdaptivePatchedData.idealConnectorSecondClosedEdge_disjoint_incomingPortTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealIncidentSeparation.lean)
-/
@[path]
private lemma idealConnectorSecondClosedEdge_disjoint_incomingPortTail_eq
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
  Disjoint (kwRawClosedEdge patch.idealVertex (kwStairOddIndex i (Fin.last M))) ({polygon.vertex (i + 1) + patch.alpha (i + 1) * (-polygon.edgeVector i)} ∪ kwTranslatedOpenRayTail (polygon.vertex (i + 1)) (patch.alpha (i + 1) * (-polygon.edgeVector i))) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealConnectorSecondClosedEdge_disjoint_incomingPortTail patch hcross hcoords i


-- created on 2026-10-23
