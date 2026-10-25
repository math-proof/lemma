import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRawSimpleFromEdges
open StatMech StatMech.FrontierA


/--
[kwRaw_vertex_injective_of_cross_nonincident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRawSimpleFromEdges.lean)
-/
@[path]
private lemma kwRaw_vertex_injective_of_cross_nonincident_eq
  {n : ℕ}
  [NeZero n]
  {vertex : Fin n → ℂ}
-- given
  (hcross : ∀ i : Fin n, kwComplexCross (kwRawEdge vertex i) (kwRawEdge vertex (i + 1)) ≠ 0)
  (hedges : ∀ i j : Fin n, KWEdgesNonincident i j → Disjoint (kwRawClosedEdge vertex i) (kwRawClosedEdge vertex j)) :
-- imply
  Function.Injective vertex := by
-- proof
  apply StatMech.FrontierA.kwRaw_vertex_injective_of_cross_nonincident vertex hcross hedges

/--
[KWRawSimplePolygonData.of_cross_nonincident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRawSimpleFromEdges.lean)
-/
@[path]
private lemma of_cross_nonincident_eq
  {n : ℕ}
  [NeZero n]
  {vertex : Fin n → ℂ}
-- given
  (hthree : 3 ≤ n)
  (hcross : ∀ i : Fin n, kwComplexCross (kwRawEdge vertex i) (kwRawEdge vertex (i + 1)) ≠ 0)
  (hedges : ∀ i j : Fin n, KWEdgesNonincident i j → Disjoint (kwRawClosedEdge vertex i) (kwRawClosedEdge vertex j)) :
-- imply
  KWRawSimplePolygonData vertex where three_le := by
-- proof
  apply StatMech.FrontierA.KWRawSimplePolygonData.of_cross_nonincident vertex hthree hcross hedges

/--
[KWStairParameterData.rawSimplePolygonData_of_nonincident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRawSimpleFromEdges.lean)
-/
@[path]
private lemma rawSimplePolygonData_of_nonincident_eq
  {n M : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
-- given
  (data : KWStairParameterData (S := M + 1) polygon)
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
  (hedges : ∀ i j : Fin (n * (2 * (M + 1))), KWEdgesNonincident i j → Disjoint (kwRawClosedEdge data.vertex i) (kwRawClosedEdge data.vertex j)) :
-- imply
  KWRawSimplePolygonData data.vertex := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.rawSimplePolygonData_of_nonincident data hcoords hedges


-- created on 2026-10-23
