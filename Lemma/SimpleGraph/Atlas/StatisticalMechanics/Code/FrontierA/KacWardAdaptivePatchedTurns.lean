import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptivePatchedTurns
open StatMech StatMech.FrontierA


/--
[KWAdaptivePatchedData.middleDelta_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedTurns.lean)
-/
@[path]
private lemma middleDelta_pos_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  0 < patch.data.parameter i q.succ.castSucc.succ - patch.data.parameter i q.succ.castSucc.castSucc := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.middleDelta_pos patch i q

/--
[KWAdaptivePatchedData.rawEdge_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedTurns.lean)
-/
@[path]
private lemma rawEdge_ne_zero_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0) :
-- imply
  ∀ j : Fin (n * (2 * (M + 1))), kwRawEdge patch.vertex j ≠ 0 := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.rawEdge_ne_zero patch hcoords

/--
[KWAdaptivePatchedData.turnAdmissible_even_middle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedTurns.lean)
-/
@[path]
private lemma turnAdmissible_even_middle_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0) :
-- imply
  KWRawTurnAdmissible patch.vertex (kwStairEvenIndex i q.castSucc) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.turnAdmissible_even_middle patch hcoords i q

/--
[KWAdaptivePatchedData.turnAdmissible_even_connector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedTurns.lean)
-/
@[path]
private lemma turnAdmissible_even_connector_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  KWRawTurnAdmissible patch.vertex (kwStairEvenIndex i (Fin.last M)) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.turnAdmissible_even_connector patch i

/--
[KWAdaptivePatchedData.sliceUsesVerticalFirst_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedTurns.lean)
-/
@[path]
private lemma sliceUsesVerticalFirst_zero_iff_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  patch.sliceUsesVerticalFirst i 0 ↔ patch.connectorUsesVerticalFirst i := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.sliceUsesVerticalFirst_zero_iff patch i

/--
[KWAdaptivePatchedData.sliceUsesVerticalFirst_last_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedTurns.lean)
-/
@[path]
private lemma sliceUsesVerticalFirst_last_iff_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  patch.sliceUsesVerticalFirst i patch.lastMiddleIndex ↔ patch.connectorUsesVerticalFirst (i + 1) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.sliceUsesVerticalFirst_last_iff patch i

/--
[KWAdaptivePatchedData.connector_corner_eq_vh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedTurns.lean)
-/
@[path]
private lemma connector_corner_eq_vh_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (h : patch.connectorUsesVerticalFirst i) :
-- imply
  (patch.connector i).corner = kwVHConnectorCorner (patch.alpha i * (-polygon.edgeVector (i - 1))) (patch.beta * polygon.edgeVector i) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.connector_corner_eq_vh patch h

/--
[KWAdaptivePatchedData.connector_corner_eq_hv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedTurns.lean)
-/
@[path]
private lemma connector_corner_eq_hv_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (h : ¬patch.connectorUsesVerticalFirst i) :
-- imply
  (patch.connector i).corner = kwHVConnectorCorner (patch.alpha i * (-polygon.edgeVector (i - 1))) (patch.beta * polygon.edgeVector i) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.connector_corner_eq_hv patch h

/--
[KWAdaptivePatchedData.connector_first_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedTurns.lean)
-/
@[path]
private lemma connector_first_eq_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  (patch.connector i).corner - patch.alpha i * (-polygon.edgeVector (i - 1)) = if patch.connectorUsesVerticalFirst i then kwVerticalPart (patch.beta * polygon.edgeVector i - patch.alpha i * (-polygon.edgeVector (i - 1))) else kwHorizontalPart (patch.beta * polygon.edgeVector i - patch.alpha i * (-polygon.edgeVector (i - 1))) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.connector_first_eq patch i

/--
[KWAdaptivePatchedData.connector_second_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedTurns.lean)
-/
@[path]
private lemma connector_second_eq_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  patch.beta * polygon.edgeVector i - (patch.connector i).corner = if patch.connectorUsesVerticalFirst i then kwHorizontalPart (patch.beta * polygon.edgeVector i - patch.alpha i * (-polygon.edgeVector (i - 1))) else kwVerticalPart (patch.beta * polygon.edgeVector i - patch.alpha i * (-polygon.edgeVector (i - 1))) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.connector_second_eq patch i

/--
[KWAdaptivePatchedData.connector_total_im_ne_of_vh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedTurns.lean)
-/
@[path]
private lemma connector_total_im_ne_of_vh_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hv : patch.connectorUsesVerticalFirst i) :
-- imply
  (patch.beta * polygon.edgeVector i - patch.alpha i * (-polygon.edgeVector (i - 1))).im ≠ 0 := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.connector_total_im_ne_of_vh patch hv

/--
[KWAdaptivePatchedData.connector_total_re_ne_of_hv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedTurns.lean)
-/
@[path]
private lemma connector_total_re_ne_of_hv_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hv : ¬patch.connectorUsesVerticalFirst i) :
-- imply
  (patch.beta * polygon.edgeVector i - patch.alpha i * (-polygon.edgeVector (i - 1))).re ≠ 0 := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.connector_total_re_ne_of_hv patch hv

/--
[KWAdaptivePatchedData.connector_total_re_ne_of_vh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedTurns.lean)
-/
@[path]
private lemma connector_total_re_ne_of_vh_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hv : patch.connectorUsesVerticalFirst i) :
-- imply
  (patch.beta * polygon.edgeVector i - patch.alpha i * (-polygon.edgeVector (i - 1))).re ≠ 0 := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.connector_total_re_ne_of_vh patch hv

/--
[KWAdaptivePatchedData.connector_total_im_ne_of_hv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedTurns.lean)
-/
@[path]
private lemma connector_total_im_ne_of_hv_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hv : ¬patch.connectorUsesVerticalFirst i) :
-- imply
  (patch.beta * polygon.edgeVector i - patch.alpha i * (-polygon.edgeVector (i - 1))).im ≠ 0 := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.connector_total_im_ne_of_hv patch hv

/--
[KWAdaptivePatchedData.turnAdmissible_lastMiddle_connector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedTurns.lean)
-/
@[path]
private lemma turnAdmissible_lastMiddle_connector_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0) :
-- imply
  KWRawTurnAdmissible patch.vertex (kwStairOddIndex i patch.lastMiddleIndex.castSucc) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.turnAdmissible_lastMiddle_connector patch hcoords i

/--
[KWAdaptivePatchedData.turnAdmissible_connector_firstMiddle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedTurns.lean)
-/
@[path]
private lemma turnAdmissible_connector_firstMiddle_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0) :
-- imply
  KWRawTurnAdmissible patch.vertex (kwStairOddIndex i (Fin.last M)) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.turnAdmissible_connector_firstMiddle patch hcoords i

/--
[KWAdaptivePatchedData.turnAdmissible_betweenMiddle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedTurns.lean)
-/
@[path]
private lemma turnAdmissible_betweenMiddle_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
  (hq : q ≠ patch.lastMiddleIndex) :
-- imply
  KWRawTurnAdmissible patch.vertex (kwStairOddIndex i q.castSucc) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.turnAdmissible_betweenMiddle patch hcoords i q hq

/--
[KWAdaptivePatchedData.turnAdmissible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedTurns.lean)
-/
@[path]
private lemma turnAdmissible_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0) :
-- imply
  ∀ j : Fin (n * (2 * (M + 1))), KWRawTurnAdmissible patch.vertex j := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.turnAdmissible patch hcoords


-- created on 2026-10-23
