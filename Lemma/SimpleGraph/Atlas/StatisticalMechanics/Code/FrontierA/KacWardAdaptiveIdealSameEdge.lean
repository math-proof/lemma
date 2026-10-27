import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveIdealSameEdge.Part2
open StatMech StatMech.FrontierA


/--
[KWAdaptivePatchedData.parameter_lt_idealMid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealSameEdge.lean)
-/
@[path]
private lemma parameter_lt_idealMid_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  patch.data.parameter i q.succ.castSucc.castSucc < patch.idealMidParameter i q := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.parameter_lt_idealMid patch i q

/--
[KWAdaptivePatchedData.idealMid_lt_parameter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealSameEdge.lean)
-/
@[path]
private lemma idealMid_lt_parameter_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  patch.idealMidParameter i q < patch.data.parameter i q.succ.castSucc.succ := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealMid_lt_parameter patch i q

/--
[KWAdaptivePatchedData.idealMiddleCorner_eq_lineMap_midParameter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealSameEdge.lean)
-/
@[path]
private lemma idealMiddleCorner_eq_lineMap_midParameter_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  patch.idealMiddleCorner i q = AffineMap.lineMap (polygon.vertex i) (polygon.vertex (i + 1)) (patch.idealMidParameter i q) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealMiddleCorner_eq_lineMap_midParameter patch i q

/--
[KWAdaptivePatchedData.idealRawClosedEdge_even_eq_parameterSegment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealSameEdge.lean)
-/
@[path]
private lemma idealRawClosedEdge_even_eq_parameterSegment_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i q.castSucc) = segment ℝ (AffineMap.lineMap (polygon.vertex i) (polygon.vertex (i + 1)) (patch.data.parameter i q.succ.castSucc.castSucc)) (AffineMap.lineMap (polygon.vertex i) (polygon.vertex (i + 1)) (patch.idealMidParameter i q)) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealRawClosedEdge_even_eq_parameterSegment patch i q

/--
[KWAdaptivePatchedData.idealRawClosedEdge_odd_eq_parameterSegment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealSameEdge.lean)
-/
@[path]
private lemma idealRawClosedEdge_odd_eq_parameterSegment_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  kwRawClosedEdge patch.idealVertex (kwStairOddIndex i q.castSucc) = segment ℝ (AffineMap.lineMap (polygon.vertex i) (polygon.vertex (i + 1)) (patch.idealMidParameter i q)) (AffineMap.lineMap (polygon.vertex i) (polygon.vertex (i + 1)) (patch.data.parameter i q.succ.castSucc.succ)) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealRawClosedEdge_odd_eq_parameterSegment patch i q

/--
[KWAdaptivePatchedData.idealRawClosedEdge_even_disjoint_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealSameEdge.lean)
-/
@[path]
private lemma idealRawClosedEdge_even_disjoint_even_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q k : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hqk : q ≠ k) :
-- imply
  Disjoint (kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i q.castSucc)) (kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i k.castSucc)) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealRawClosedEdge_even_disjoint_even patch i q k hqk

/--
[KWAdaptivePatchedData.idealRawClosedEdge_odd_disjoint_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealSameEdge.lean)
-/
@[path]
private lemma idealRawClosedEdge_odd_disjoint_odd_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q k : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hqk : q ≠ k) :
-- imply
  Disjoint (kwRawClosedEdge patch.idealVertex (kwStairOddIndex i q.castSucc)) (kwRawClosedEdge patch.idealVertex (kwStairOddIndex i k.castSucc)) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealRawClosedEdge_odd_disjoint_odd patch i q k hqk

/--
[KWAdaptivePatchedData.idealRawClosedEdge_even_disjoint_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealSameEdge.lean)
-/
@[path]
private lemma idealRawClosedEdge_even_disjoint_odd_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q k : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hnon : KWEdgesNonincident (kwStairEvenIndex i q.castSucc) (kwStairOddIndex i k.castSucc)) :
-- imply
  Disjoint (kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i q.castSucc)) (kwRawClosedEdge patch.idealVertex (kwStairOddIndex i k.castSucc)) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealRawClosedEdge_even_disjoint_odd patch i q k hnon

/--
[KWAdaptivePatchedData.idealRawClosedEdge_odd_disjoint_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealSameEdge.lean)
-/
@[path]
private lemma idealRawClosedEdge_odd_disjoint_even_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q k : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hnon : KWEdgesNonincident (kwStairOddIndex i q.castSucc) (kwStairEvenIndex i k.castSucc)) :
-- imply
  Disjoint (kwRawClosedEdge patch.idealVertex (kwStairOddIndex i q.castSucc)) (kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i k.castSucc)) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealRawClosedEdge_odd_disjoint_even patch i q k hnon


-- created on 2026-10-23
