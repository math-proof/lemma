import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveIdealSimple.Part2
open StatMech StatMech.FrontierA


/--
[KWSmallAdaptiveConnectorScales.idealRawSimpleData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealSimple.lean)
-/
@[path]
private lemma idealRawSimpleData_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {neighborhood : KWVertexNeighborhoodData polygon}
  {scales : KWSmallAdaptiveConnectorScales polygon neighborhood.scale}
-- given
  (hM : 2 ≤ M)
  (hcross : ∀ i : Fin n, kwComplexCross (polygon.edgeVector i) (polygon.edgeVector (i + 1)) ≠ 0)
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0) :
-- imply
  let patch := scales.toPatchedData hM KWRawNonbacktrackingSimpleData patch.idealVertex := by
-- proof
  apply StatMech.FrontierA.KWSmallAdaptiveConnectorScales.idealRawSimpleData neighborhood scales hM hcross hcoords

/--
[KWSmallAdaptiveConnectorScales.idealSimplePolygon_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealSimple.lean)
-/
@[path]
private lemma idealSimplePolygon_vertex_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {neighborhood : KWVertexNeighborhoodData polygon}
  {scales : KWSmallAdaptiveConnectorScales polygon neighborhood.scale}
-- given
  (hM : 2 ≤ M)
  (hcross : ∀ i : Fin n, kwComplexCross (polygon.edgeVector i) (polygon.edgeVector (i + 1)) ≠ 0)
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0) :
-- imply
  (scales.idealSimplePolygon neighborhood hM hcross hcoords).vertex = (scales.toPatchedData hM).idealVertex := by
-- proof
  apply StatMech.FrontierA.KWSmallAdaptiveConnectorScales.idealSimplePolygon_vertex neighborhood scales hM hcross hcoords


-- created on 2026-10-23
