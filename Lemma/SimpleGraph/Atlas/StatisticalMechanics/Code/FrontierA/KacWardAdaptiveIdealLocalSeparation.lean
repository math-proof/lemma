import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveIdealLocalSeparation
open StatMech StatMech.FrontierA


/--
[KWAdaptivePatchedData.idealFirstConnector_disjoint_outgoingMiddle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealLocalSeparation.lean)
-/
@[path]
private lemma idealFirstConnector_disjoint_outgoingMiddle_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
  {even : Bool}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j) (polygon.edgeVector (j + 1)) ≠ 0)
  (hcoords : ∀ j : Fin n, (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0) :
-- imply
  Disjoint (kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i (Fin.last M))) (patch.idealMiddleClosedEdge (i + 1) q even) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealFirstConnector_disjoint_outgoingMiddle patch hcross hcoords i q even

/--
[KWAdaptivePatchedData.idealSecondConnector_disjoint_incomingMiddle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealLocalSeparation.lean)
-/
@[path]
private lemma idealSecondConnector_disjoint_incomingMiddle_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
  {even : Bool}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j) (polygon.edgeVector (j + 1)) ≠ 0)
  (hcoords : ∀ j : Fin n, (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0) :
-- imply
  Disjoint (kwRawClosedEdge patch.idealVertex (kwStairOddIndex i (Fin.last M))) (patch.idealMiddleClosedEdge i q even) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealSecondConnector_disjoint_incomingMiddle patch hcross hcoords i q even

/--
[KWAdaptivePatchedData.idealConnector_disjoint_incomingMiddle_of_notLastOdd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealLocalSeparation.lean)
-/
@[path]
private lemma idealConnector_disjoint_incomingMiddle_of_notLastOdd_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
  {even : Bool}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j) (polygon.edgeVector (j + 1)) ≠ 0)
  (hcoords : ∀ j : Fin n, (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
  (hnotLast : q ≠ patch.lastMiddleIndex ∨ even = true) :
-- imply
  Disjoint (kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i (Fin.last M)) ∪ kwRawClosedEdge patch.idealVertex (kwStairOddIndex i (Fin.last M))) (patch.idealMiddleClosedEdge i q even) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealConnector_disjoint_incomingMiddle_of_notLastOdd patch hcross hcoords i q even hnotLast

/--
[KWAdaptivePatchedData.idealConnector_disjoint_outgoingMiddle_of_notFirstEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealLocalSeparation.lean)
-/
@[path]
private lemma idealConnector_disjoint_outgoingMiddle_of_notFirstEven_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
  {even : Bool}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j) (polygon.edgeVector (j + 1)) ≠ 0)
  (hcoords : ∀ j : Fin n, (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
  (hnotFirst : q ≠ 0 ∨ even = false) :
-- imply
  Disjoint (kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i (Fin.last M)) ∪ kwRawClosedEdge patch.idealVertex (kwStairOddIndex i (Fin.last M))) (patch.idealMiddleClosedEdge (i + 1) q even) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealConnector_disjoint_outgoingMiddle_of_notFirstEven patch hcross hcoords i q even hnotFirst


-- created on 2026-10-23
