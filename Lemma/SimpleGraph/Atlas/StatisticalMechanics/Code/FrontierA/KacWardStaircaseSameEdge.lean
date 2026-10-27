import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStaircaseSameEdge
open StatMech StatMech.FrontierA


/--
[KWStairParameterData.horizontalLeg_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseSameEdge.lean)
-/
@[path]
private lemma horizontalLeg_disjoint_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k q : Fin S}
-- given
  (data : KWStairParameterData (S := S) polygon)
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
  (hkq : k ≠ q) :
-- imply
  Disjoint (segment ℝ (data.base i k.castSucc) (data.corner i k)) (segment ℝ (data.base i q.castSucc) (data.corner i q)) := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.horizontalLeg_disjoint data hcoords i hkq

/--
[KWStairParameterData.verticalLeg_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseSameEdge.lean)
-/
@[path]
private lemma verticalLeg_disjoint_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k q : Fin S}
-- given
  (data : KWStairParameterData (S := S) polygon)
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
  (hkq : k ≠ q) :
-- imply
  Disjoint (segment ℝ (data.corner i k) (data.base i k.succ)) (segment ℝ (data.corner i q) (data.base i q.succ)) := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.verticalLeg_disjoint data hcoords i hkq

/--
[KWStairParameterData.horizontalLeg_disjoint_verticalLeg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseSameEdge.lean)
-/
@[path]
private lemma horizontalLeg_disjoint_verticalLeg_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k q : Fin S}
-- given
  (data : KWStairParameterData (S := S) polygon)
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
  (hkq : k ≠ q)
  (hprev : q.val + 1 ≠ k.val) :
-- imply
  Disjoint (segment ℝ (data.base i k.castSucc) (data.corner i k)) (segment ℝ (data.corner i q) (data.base i q.succ)) := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.horizontalLeg_disjoint_verticalLeg data hcoords i hkq hprev

/--
[KWStairParameterData.verticalLeg_disjoint_horizontalLeg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseSameEdge.lean)
-/
@[path]
private lemma verticalLeg_disjoint_horizontalLeg_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k q : Fin S}
-- given
  (data : KWStairParameterData (S := S) polygon)
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
  (hkq : k ≠ q)
  (hsucc : k.val + 1 ≠ q.val) :
-- imply
  Disjoint (segment ℝ (data.corner i k) (data.base i k.succ)) (segment ℝ (data.base i q.castSucc) (data.corner i q)) := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.verticalLeg_disjoint_horizontalLeg data hcoords i hkq hsucc

/--
[KWStairParameterData.rawClosedEdge_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseSameEdge.lean)
-/
@[path]
private lemma rawClosedEdge_even_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k : Fin S}
-- given
  (data : KWStairParameterData (S := S) polygon) :
-- imply
  kwRawClosedEdge data.vertex (kwStairEvenIndex i k) = segment ℝ (data.base i k.castSucc) (data.corner i k) := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.rawClosedEdge_even data i k

/--
[KWStairParameterData.rawClosedEdge_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseSameEdge.lean)
-/
@[path]
private lemma rawClosedEdge_odd_eq
  {n M : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k : Fin (M + 1)}
-- given
  (data : KWStairParameterData (S := M + 1) polygon) :
-- imply
  kwRawClosedEdge data.vertex (kwStairOddIndex i k) = segment ℝ (data.corner i k) (data.base i k.succ) := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.rawClosedEdge_odd data i k

/--
[KWStairParameterData.rawClosedEdge_even_disjoint_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseSameEdge.lean)
-/
@[path]
private lemma rawClosedEdge_even_disjoint_even_eq
  {n M : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k q : Fin (M + 1)}
-- given
  (data : KWStairParameterData (S := M + 1) polygon)
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
  (hnon : KWEdgesNonincident (kwStairEvenIndex i k) (kwStairEvenIndex i q)) :
-- imply
  Disjoint (kwRawClosedEdge data.vertex (kwStairEvenIndex i k)) (kwRawClosedEdge data.vertex (kwStairEvenIndex i q)) := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.rawClosedEdge_even_disjoint_even data hcoords i k q hnon

/--
[KWStairParameterData.rawClosedEdge_odd_disjoint_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseSameEdge.lean)
-/
@[path]
private lemma rawClosedEdge_odd_disjoint_odd_eq
  {n M : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k q : Fin (M + 1)}
-- given
  (data : KWStairParameterData (S := M + 1) polygon)
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
  (hnon : KWEdgesNonincident (kwStairOddIndex i k) (kwStairOddIndex i q)) :
-- imply
  Disjoint (kwRawClosedEdge data.vertex (kwStairOddIndex i k)) (kwRawClosedEdge data.vertex (kwStairOddIndex i q)) := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.rawClosedEdge_odd_disjoint_odd data hcoords i k q hnon

/--
[KWStairParameterData.rawClosedEdge_even_disjoint_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseSameEdge.lean)
-/
@[path]
private lemma rawClosedEdge_even_disjoint_odd_eq
  {n M : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k q : Fin (M + 1)}
-- given
  (data : KWStairParameterData (S := M + 1) polygon)
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
  (hnon : KWEdgesNonincident (kwStairEvenIndex i k) (kwStairOddIndex i q)) :
-- imply
  Disjoint (kwRawClosedEdge data.vertex (kwStairEvenIndex i k)) (kwRawClosedEdge data.vertex (kwStairOddIndex i q)) := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.rawClosedEdge_even_disjoint_odd data hcoords i k q hnon

/--
[KWStairParameterData.rawClosedEdge_odd_disjoint_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseSameEdge.lean)
-/
@[path]
private lemma rawClosedEdge_odd_disjoint_even_eq
  {n M : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k q : Fin (M + 1)}
-- given
  (data : KWStairParameterData (S := M + 1) polygon)
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
  (hnon : KWEdgesNonincident (kwStairOddIndex i k) (kwStairEvenIndex i q)) :
-- imply
  Disjoint (kwRawClosedEdge data.vertex (kwStairOddIndex i k)) (kwRawClosedEdge data.vertex (kwStairEvenIndex i q)) := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.rawClosedEdge_odd_disjoint_even data hcoords i k q hnon

/--
[KWStairParameterData.rawClosedEdges_disjoint_sameOwner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseSameEdge.lean)
-/
@[path]
private lemma rawClosedEdges_disjoint_sameOwner_eq
  {n M : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {j l : Fin (n * (2 * (M + 1)))}
-- given
  (data : KWStairParameterData (S := M + 1) polygon)
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
  (hj : (finProdFinEquiv.symm j).1 = i)
  (hl : (finProdFinEquiv.symm l).1 = i)
  (hnon : KWEdgesNonincident j l) :
-- imply
  Disjoint (kwRawClosedEdge data.vertex j) (kwRawClosedEdge data.vertex l) := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.rawClosedEdges_disjoint_sameOwner data hcoords i j l hj hl hnon


-- created on 2026-10-23
