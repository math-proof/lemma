import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveIdealIncidentEdges
open StatMech StatMech.FrontierA


/--
[KWAdaptivePatchedData.idealConnectorFirst_disjoint_outgoingEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealIncidentEdges.lean)
-/
@[path]
private lemma idealConnectorFirst_disjoint_outgoingEven_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j) (polygon.edgeVector (j + 1)) ≠ 0)
  (hcoords : ∀ j : Fin n, (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0) :
-- imply
  Disjoint (kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i (Fin.last M))) (kwRawClosedEdge patch.idealVertex (kwStairEvenIndex (i + 1) q.castSucc)) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealConnectorFirst_disjoint_outgoingEven patch hcross hcoords i q

/--
[KWAdaptivePatchedData.idealConnectorFirst_disjoint_outgoingOdd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealIncidentEdges.lean)
-/
@[path]
private lemma idealConnectorFirst_disjoint_outgoingOdd_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j) (polygon.edgeVector (j + 1)) ≠ 0)
  (hcoords : ∀ j : Fin n, (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0) :
-- imply
  Disjoint (kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i (Fin.last M))) (kwRawClosedEdge patch.idealVertex (kwStairOddIndex (i + 1) q.castSucc)) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealConnectorFirst_disjoint_outgoingOdd patch hcross hcoords i q

/--
[KWAdaptivePatchedData.idealConnectorSecond_disjoint_incomingEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealIncidentEdges.lean)
-/
@[path]
private lemma idealConnectorSecond_disjoint_incomingEven_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j) (polygon.edgeVector (j + 1)) ≠ 0)
  (hcoords : ∀ j : Fin n, (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0) :
-- imply
  Disjoint (kwRawClosedEdge patch.idealVertex (kwStairOddIndex i (Fin.last M))) (kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i q.castSucc)) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealConnectorSecond_disjoint_incomingEven patch hcross hcoords i q

/--
[KWAdaptivePatchedData.idealConnectorSecond_disjoint_incomingOdd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealIncidentEdges.lean)
-/
@[path]
private lemma idealConnectorSecond_disjoint_incomingOdd_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j) (polygon.edgeVector (j + 1)) ≠ 0)
  (hcoords : ∀ j : Fin n, (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0) :
-- imply
  Disjoint (kwRawClosedEdge patch.idealVertex (kwStairOddIndex i (Fin.last M))) (kwRawClosedEdge patch.idealVertex (kwStairOddIndex i q.castSucc)) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealConnectorSecond_disjoint_incomingOdd patch hcross hcoords i q

/--
[KWAdaptivePatchedData.idealConnectorFirst_disjoint_incomingEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealIncidentEdges.lean)
-/
@[path]
private lemma idealConnectorFirst_disjoint_incomingEven_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j) (polygon.edgeVector (j + 1)) ≠ 0)
  (hcoords : ∀ j : Fin n, (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0) :
-- imply
  Disjoint (kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i (Fin.last M))) (kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i q.castSucc)) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealConnectorFirst_disjoint_incomingEven patch hcross hcoords i q

/--
[KWAdaptivePatchedData.idealConnectorFirst_disjoint_incomingOdd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealIncidentEdges.lean)
-/
@[path]
private lemma idealConnectorFirst_disjoint_incomingOdd_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j) (polygon.edgeVector (j + 1)) ≠ 0)
  (hcoords : ∀ j : Fin n, (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
  (hq : q ≠ patch.lastMiddleIndex) :
-- imply
  Disjoint (kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i (Fin.last M))) (kwRawClosedEdge patch.idealVertex (kwStairOddIndex i q.castSucc)) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealConnectorFirst_disjoint_incomingOdd patch hcross hcoords i q hq

/--
[KWAdaptivePatchedData.idealConnectorSecond_disjoint_outgoingEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealIncidentEdges.lean)
-/
@[path]
private lemma idealConnectorSecond_disjoint_outgoingEven_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j) (polygon.edgeVector (j + 1)) ≠ 0)
  (hcoords : ∀ j : Fin n, (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
  (hq : q ≠ 0) :
-- imply
  Disjoint (kwRawClosedEdge patch.idealVertex (kwStairOddIndex i (Fin.last M))) (kwRawClosedEdge patch.idealVertex (kwStairEvenIndex (i + 1) q.castSucc)) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealConnectorSecond_disjoint_outgoingEven patch hcross hcoords i q hq

/--
[KWAdaptivePatchedData.idealConnectorSecond_disjoint_outgoingOdd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealIncidentEdges.lean)
-/
@[path]
private lemma idealConnectorSecond_disjoint_outgoingOdd_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j) (polygon.edgeVector (j + 1)) ≠ 0)
  (hcoords : ∀ j : Fin n, (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0) :
-- imply
  Disjoint (kwRawClosedEdge patch.idealVertex (kwStairOddIndex i (Fin.last M))) (kwRawClosedEdge patch.idealVertex (kwStairOddIndex (i + 1) q.castSucc)) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealConnectorSecond_disjoint_outgoingOdd patch hcross hcoords i q


-- created on 2026-10-23
