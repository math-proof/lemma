import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveActualPhaseModel
open StatMech StatMech.FrontierA


/--
[KWAdaptivePatchedData.rawEdge_axis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualPhaseModel.lean)
-/
@[path]
private lemma rawEdge_axis_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  ∀ j, (kwRawEdge patch.vertex j).re = 0 ∨ (kwRawEdge patch.vertex j).im = 0 := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.rawEdge_axis patch

/--
[KWSmallAdaptiveConnectorScales.exists_actualSimplePhaseModel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualPhaseModel.lean)
-/
@[path]
private lemma exists_actualSimplePhaseModel_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {neighborhood : KWVertexNeighborhoodData polygon}
  {scales : KWSmallAdaptiveConnectorScales polygon neighborhood.scale}
-- given
  (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j) (polygon.edgeVector (j + 1)) ≠ 0)
  (hcoords : ∀ j : Fin n, (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0) :
-- imply
  ∃ M : ℕ, ∃ inst : NeZero M, ∃ hM : 2 ≤ M, letI : NeZero M := inst ∃ actual : KWFiniteSimplePolygon (n * (2 * (M + 1))), actual.vertex = (scales.toPatchedData hM).vertex ∧ kwVectorPhaseCycle actual.edgeList = kwVectorPhaseCycle (List.ofFn (kwRawEdge (scales.toPatchedData hM).idealVertex)) := by
-- proof
  apply StatMech.FrontierA.KWSmallAdaptiveConnectorScales.exists_actualSimplePhaseModel neighborhood scales hcross hcoords

/--
[KWSmallAdaptiveConnectorScales.exists_actualSimpleSourcePhaseModel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualPhaseModel.lean)
-/
@[path]
private lemma exists_actualSimpleSourcePhaseModel_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {neighborhood : KWVertexNeighborhoodData polygon}
  {scales : KWSmallAdaptiveConnectorScales polygon neighborhood.scale}
-- given
  (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j) (polygon.edgeVector (j + 1)) ≠ 0)
  (hcoords : ∀ j : Fin n, (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0) :
-- imply
  ∃ M : ℕ, ∃ inst : NeZero M, ∃ hM : 2 ≤ M, letI : NeZero M := inst ∃ actual : KWFiniteSimplePolygon (n * (2 * (M + 1))), actual.vertex = (scales.toPatchedData hM).vertex ∧ kwVectorPhaseCycle actual.edgeList = kwVectorPhaseCycle polygon.edgeList := by
-- proof
  apply StatMech.FrontierA.KWSmallAdaptiveConnectorScales.exists_actualSimpleSourcePhaseModel neighborhood scales hcross hcoords

/--
[KWFiniteSimplePolygon.phaseCycle_eq_neg_one_of_generic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualPhaseModel.lean)
-/
@[path]
private lemma phaseCycle_eq_neg_one_of_generic_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
-- given
  (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j) (polygon.edgeVector (j + 1)) ≠ 0)
  (hcoords : ∀ j : Fin n, (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0) :
-- imply
  kwVectorPhaseCycle polygon.edgeList = -1 := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.phaseCycle_eq_neg_one_of_generic polygon hcross hcoords


-- created on 2026-10-23
