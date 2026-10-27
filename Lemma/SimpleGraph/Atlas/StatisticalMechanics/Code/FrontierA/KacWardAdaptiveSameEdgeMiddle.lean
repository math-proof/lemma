import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveSameEdgeMiddle.Part2
open StatMech StatMech.FrontierA


/--
[KWAdaptivePatchedData.middleCorner_re](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveSameEdgeMiddle.lean)
-/
@[path]
private lemma middleCorner_re_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  (patch.middleCorner i q).re = (polygon.vertex i).re + (if patch.sliceUsesVerticalFirst i q then patch.data.parameter i q.succ.castSucc.castSucc else patch.data.parameter i q.succ.castSucc.succ) * (polygon.edgeVector i).re := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.middleCorner_re patch i q

/--
[KWAdaptivePatchedData.middleCorner_im](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveSameEdgeMiddle.lean)
-/
@[path]
private lemma middleCorner_im_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  (patch.middleCorner i q).im = (polygon.vertex i).im + (if patch.sliceUsesVerticalFirst i q then patch.data.parameter i q.succ.castSucc.succ else patch.data.parameter i q.succ.castSucc.castSucc) * (polygon.edgeVector i).im := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.middleCorner_im patch i q

/--
[KWAdaptivePatchedData.pathBase_castSucc_re](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveSameEdgeMiddle.lean)
-/
@[path]
private lemma pathBase_castSucc_re_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  (patch.pathBase i q.castSucc).re = (polygon.vertex i).re + patch.data.parameter i q.succ.castSucc.castSucc * (polygon.edgeVector i).re := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.pathBase_castSucc_re patch i q

/--
[KWAdaptivePatchedData.pathBase_castSucc_im](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveSameEdgeMiddle.lean)
-/
@[path]
private lemma pathBase_castSucc_im_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  (patch.pathBase i q.castSucc).im = (polygon.vertex i).im + patch.data.parameter i q.succ.castSucc.castSucc * (polygon.edgeVector i).im := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.pathBase_castSucc_im patch i q

/--
[KWAdaptivePatchedData.pathBase_succ_re](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveSameEdgeMiddle.lean)
-/
@[path]
private lemma pathBase_succ_re_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  (patch.pathBase i q.succ).re = (polygon.vertex i).re + patch.data.parameter i q.succ.castSucc.succ * (polygon.edgeVector i).re := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.pathBase_succ_re patch i q

/--
[KWAdaptivePatchedData.pathBase_succ_im](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveSameEdgeMiddle.lean)
-/
@[path]
private lemma pathBase_succ_im_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  (patch.pathBase i q.succ).im = (polygon.vertex i).im + patch.data.parameter i q.succ.castSucc.succ * (polygon.edgeVector i).im := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.pathBase_succ_im patch i q

/--
[KWAdaptivePatchedData.middle_rawClosedEdge_point_parameters](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveSameEdgeMiddle.lean)
-/
@[path]
private lemma middle_rawClosedEdge_point_parameters_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
  {even : Bool}
  {z : ℂ}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hz : z ∈ if even then kwRawClosedEdge patch.vertex (kwStairEvenIndex i q.castSucc) else kwRawClosedEdge patch.vertex (kwStairOddIndex i q.castSucc)) :
-- imply
  (∃ u ∈ Icc (patch.data.parameter i q.succ.castSucc.castSucc) (patch.data.parameter i q.succ.castSucc.succ), z.re = (polygon.vertex i).re + u * (polygon.edgeVector i).re) ∧ (∃ u ∈ Icc (patch.data.parameter i q.succ.castSucc.castSucc) (patch.data.parameter i q.succ.castSucc.succ), z.im = (polygon.vertex i).im + u * (polygon.edgeVector i).im) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.middle_rawClosedEdge_point_parameters patch i q even hz

/--
[KWAdaptivePatchedData.pathBase_succ_not_mem_even_middle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveSameEdgeMiddle.lean)
-/
@[path]
private lemma pathBase_succ_not_mem_even_middle_eq
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
  patch.pathBase i q.succ ∉ kwRawClosedEdge patch.vertex (kwStairEvenIndex i q.castSucc) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.pathBase_succ_not_mem_even_middle patch hcoords i q

/--
[KWAdaptivePatchedData.pathBase_castSucc_not_mem_odd_middle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveSameEdgeMiddle.lean)
-/
@[path]
private lemma pathBase_castSucc_not_mem_odd_middle_eq
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
  patch.pathBase i q.castSucc ∉ kwRawClosedEdge patch.vertex (kwStairOddIndex i q.castSucc) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.pathBase_castSucc_not_mem_odd_middle patch hcoords i q

/--
[KWAdaptivePatchedData.middleClosedEdge_point_parameters](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveSameEdgeMiddle.lean)
-/
@[path]
private lemma middleClosedEdge_point_parameters_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
  {even : Bool}
  {z : ℂ}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hz : z ∈ patch.middleClosedEdge i q even) :
-- imply
  (∃ u ∈ Icc (patch.data.parameter i q.succ.castSucc.castSucc) (patch.data.parameter i q.succ.castSucc.succ), z.re = (polygon.vertex i).re + u * (polygon.edgeVector i).re) ∧ (∃ u ∈ Icc (patch.data.parameter i q.succ.castSucc.castSucc) (patch.data.parameter i q.succ.castSucc.succ), z.im = (polygon.vertex i).im + u * (polygon.edgeVector i).im) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.middleClosedEdge_point_parameters patch i q even hz

/--
[KWAdaptivePatchedData.middleClosedEdges_disjoint_sameOwner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveSameEdgeMiddle.lean)
-/
@[path]
private lemma middleClosedEdges_disjoint_sameOwner_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q l : Fin M}
  {eq el : Bool}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
  (hnon : KWEdgesNonincident (kwAdaptiveMiddleIndex i q eq) (kwAdaptiveMiddleIndex i l el)) :
-- imply
  Disjoint (patch.middleClosedEdge i q eq) (patch.middleClosedEdge i l el) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.middleClosedEdges_disjoint_sameOwner patch hcoords i q l eq el hnon


-- created on 2026-10-23
