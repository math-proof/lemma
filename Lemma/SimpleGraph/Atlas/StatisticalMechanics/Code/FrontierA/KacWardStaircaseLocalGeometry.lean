import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStaircaseLocalGeometry
open StatMech StatMech.FrontierA


/--
[kwStairParameterDelta_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseLocalGeometry.lean)
-/
@[path]
private lemma kwStairParameterDelta_pos_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k : Fin S}
-- given
  (data : KWStairParameterData (S := S) polygon) :
-- imply
  0 < data.parameter i k.succ - data.parameter i k.castSucc := by
-- proof
  apply StatMech.FrontierA.kwStairParameterDelta_pos data i k

/--
[kwStairRawEdge_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseLocalGeometry.lean)
-/
@[path]
private lemma kwStairRawEdge_even_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k : Fin S}
-- given
  (data : KWStairParameterData (S := S) polygon) :
-- imply
  kwRawEdge data.vertex (kwStairEvenIndex i k) = (data.parameter i k.succ - data.parameter i k.castSucc) * kwHorizontalPart (polygon.edgeVector i) := by
-- proof
  apply StatMech.FrontierA.kwStairRawEdge_even data i k

/--
[kwStairRawEdge_odd_castSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseLocalGeometry.lean)
-/
@[path]
private lemma kwStairRawEdge_odd_castSucc_eq
  {n M : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k : Fin M}
-- given
  (data : KWStairParameterData (S := M + 1) polygon) :
-- imply
  kwRawEdge data.vertex (kwStairOddIndex i k.castSucc) = (data.parameter i k.castSucc.succ - data.parameter i k.castSucc.castSucc) * kwVerticalPart (polygon.edgeVector i) := by
-- proof
  apply StatMech.FrontierA.kwStairRawEdge_odd_castSucc data i k

/--
[kwStairRawEdge_odd_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseLocalGeometry.lean)
-/
@[path]
private lemma kwStairRawEdge_odd_last_eq
  {n M : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (data : KWStairParameterData (S := M + 1) polygon) :
-- imply
  kwRawEdge data.vertex (kwStairOddIndex i (Fin.last M)) = (data.parameter i (Fin.last M).succ - data.parameter i (Fin.last M).castSucc) * kwVerticalPart (polygon.edgeVector i) := by
-- proof
  apply StatMech.FrontierA.kwStairRawEdge_odd_last data i

/--
[kwStairIndex_even_or_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseLocalGeometry.lean)
-/
@[path]
private lemma kwStairIndex_even_or_odd_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {j : Fin (n * (2 * S))} :
-- imply
  ∃ i : Fin n, ∃ k : Fin S, j = kwStairEvenIndex i k ∨ j = kwStairOddIndex i k := by
-- proof
  apply StatMech.FrontierA.kwStairIndex_even_or_odd j

/--
[kwStairCross_even_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseLocalGeometry.lean)
-/
@[path]
private lemma kwStairCross_even_ne_zero_eq
  {n M : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k : Fin (M + 1)}
-- given
  (data : KWStairParameterData (S := M + 1) polygon)
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0) :
-- imply
  kwComplexCross (kwRawEdge data.vertex (kwStairEvenIndex i k)) (kwRawEdge data.vertex (kwStairEvenIndex i k + 1)) ≠ 0 := by
-- proof
  apply StatMech.FrontierA.kwStairCross_even_ne_zero data hcoords i k

/--
[kwStairCross_odd_castSucc_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseLocalGeometry.lean)
-/
@[path]
private lemma kwStairCross_odd_castSucc_ne_zero_eq
  {n M : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k : Fin M}
-- given
  (data : KWStairParameterData (S := M + 1) polygon)
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0) :
-- imply
  kwComplexCross (kwRawEdge data.vertex (kwStairOddIndex i k.castSucc)) (kwRawEdge data.vertex (kwStairOddIndex i k.castSucc + 1)) ≠ 0 := by
-- proof
  apply StatMech.FrontierA.kwStairCross_odd_castSucc_ne_zero data hcoords i k

/--
[kwStairCross_odd_last_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseLocalGeometry.lean)
-/
@[path]
private lemma kwStairCross_odd_last_ne_zero_eq
  {n M : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (data : KWStairParameterData (S := M + 1) polygon)
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0) :
-- imply
  kwComplexCross (kwRawEdge data.vertex (kwStairOddIndex i (Fin.last M))) (kwRawEdge data.vertex (kwStairOddIndex i (Fin.last M) + 1)) ≠ 0 := by
-- proof
  apply StatMech.FrontierA.kwStairCross_odd_last_ne_zero data hcoords i

/--
[KWStairParameterData.cross_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseLocalGeometry.lean)
-/
@[path]
private lemma cross_ne_zero_eq
  {n M : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
-- given
  (data : KWStairParameterData (S := M + 1) polygon)
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0) :
-- imply
  ∀ j : Fin (n * (2 * (M + 1))), kwComplexCross (kwRawEdge data.vertex j) (kwRawEdge data.vertex (j + 1)) ≠ 0 := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.cross_ne_zero data hcoords

/--
[KWStairParameterData.vertex_injective_of_pairwiseLocal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseLocalGeometry.lean)
-/
@[path]
private lemma vertex_injective_of_pairwiseLocal_eq
  {n M : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
-- given
  (data : KWStairParameterData (S := M + 1) polygon)
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
  (hpair : ∀ i j : Fin n, i ≠ j → Disjoint (Set.range (data.localVertex i)) (Set.range (data.localVertex j))) :
-- imply
  Function.Injective data.vertex := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.vertex_injective_of_pairwiseLocal data hcoords hpair

/--
[KWStairParameterData.rawSimplePolygonData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseLocalGeometry.lean)
-/
@[path]
private lemma rawSimplePolygonData_eq
  {n M : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
-- given
  (data : KWStairParameterData (S := M + 1) polygon)
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
  (hpair : ∀ i j : Fin n, i ≠ j → Disjoint (Set.range (data.localVertex i)) (Set.range (data.localVertex j)))
  (hedges : ∀ i j : Fin (n * (2 * (M + 1))), KWEdgesNonincident i j → Disjoint (kwRawClosedEdge data.vertex i) (kwRawClosedEdge data.vertex j)) :
-- imply
  KWRawSimplePolygonData data.vertex where three_le := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.rawSimplePolygonData data hcoords hpair hedges

/--
[KWStairParameterData.localVertex_range_subset_closedEdgeTube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseLocalGeometry.lean)
-/
@[path]
private lemma localVertex_range_subset_closedEdgeTube_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (data : KWStairParameterData (S := S) polygon)
  (r : ℝ≥0)
  (hr : 0 < r)
  (hfine : data.MeshWithin r) :
-- imply
  Set.range (data.localVertex i) ⊆ polygon.closedEdgeTube r i := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.localVertex_range_subset_closedEdgeTube data r hr hfine i

/--
[KWStairParameterData.localVertex_ranges_disjoint_of_nonincident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseLocalGeometry.lean)
-/
@[path]
private lemma localVertex_ranges_disjoint_of_nonincident_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {polygon : KWFiniteSimplePolygon n}
  {i j : Fin n}
-- given
  (data : KWStairParameterData (S := S) polygon)
  (r : ℝ≥0)
  (hr : 0 < r)
  (hfine : data.MeshWithin r)
  (htubes : ∀ i j : Fin n, KWEdgesNonincident i j → Disjoint (polygon.closedEdgeTube r i) (polygon.closedEdgeTube r j))
  (hij : KWEdgesNonincident i j) :
-- imply
  Disjoint (Set.range (data.localVertex i)) (Set.range (data.localVertex j)) := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.localVertex_ranges_disjoint_of_nonincident data r hr hfine htubes hij

/--
[KWStairParameterData.rawClosedEdge_even_subset_closedEdgeTube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseLocalGeometry.lean)
-/
@[path]
private lemma rawClosedEdge_even_subset_closedEdgeTube_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k : Fin S}
-- given
  (data : KWStairParameterData (S := S) polygon)
  (r : ℝ≥0)
  (hr : 0 < r)
  (hfine : data.MeshWithin r) :
-- imply
  kwRawClosedEdge data.vertex (kwStairEvenIndex i k) ⊆ polygon.closedEdgeTube r i := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.rawClosedEdge_even_subset_closedEdgeTube data r hr hfine i k

/--
[KWStairParameterData.rawClosedEdge_odd_castSucc_subset_closedEdgeTube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseLocalGeometry.lean)
-/
@[path]
private lemma rawClosedEdge_odd_castSucc_subset_closedEdgeTube_eq
  {n M : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k : Fin M}
-- given
  (data : KWStairParameterData (S := M + 1) polygon)
  (r : ℝ≥0)
  (hr : 0 < r)
  (hfine : data.MeshWithin r) :
-- imply
  kwRawClosedEdge data.vertex (kwStairOddIndex i k.castSucc) ⊆ polygon.closedEdgeTube r i := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.rawClosedEdge_odd_castSucc_subset_closedEdgeTube data r hr hfine i k

/--
[KWStairParameterData.rawClosedEdge_odd_last_subset_closedEdgeTube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseLocalGeometry.lean)
-/
@[path]
private lemma rawClosedEdge_odd_last_subset_closedEdgeTube_eq
  {n M : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (data : KWStairParameterData (S := M + 1) polygon)
  (r : ℝ≥0)
  (hr : 0 < r)
  (hfine : data.MeshWithin r) :
-- imply
  kwRawClosedEdge data.vertex (kwStairOddIndex i (Fin.last M)) ⊆ polygon.closedEdgeTube r i := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.rawClosedEdge_odd_last_subset_closedEdgeTube data r hr hfine i

/--
[KWStairParameterData.rawClosedEdge_subset_ownerTube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseLocalGeometry.lean)
-/
@[path]
private lemma rawClosedEdge_subset_ownerTube_eq
  {n M : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {j : Fin (n * (2 * (M + 1)))}
-- given
  (data : KWStairParameterData (S := M + 1) polygon)
  (r : ℝ≥0)
  (hr : 0 < r)
  (hfine : data.MeshWithin r) :
-- imply
  ∃ i : Fin n, kwRawClosedEdge data.vertex j ⊆ polygon.closedEdgeTube r i := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.rawClosedEdge_subset_ownerTube data r hr hfine j


-- created on 2026-10-23
