import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveSourcePhase
open StatMech StatMech.FrontierA


/--
[KWAdaptivePatchedData.ideal_block_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveSourcePhase.lean)
-/
@[path]
private lemma ideal_block_phase_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
  (hcross : ∀ i : Fin n, kwComplexCross (polygon.edgeVector i) (polygon.edgeVector (i + 1)) ≠ 0) :
-- imply
  (∏ l : Fin (2 * (M + 1)), kwVectorTurnPhase (kwRawEdge patch.idealVertex (finProdFinEquiv (i, l))) (kwRawEdge patch.idealVertex (finProdFinEquiv (i, l) + 1))) = kwVectorTurnPhase (polygon.edgeVector i) (polygon.edgeVector (i + 1)) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.ideal_block_phase patch hcoords hcross i

/--
[KWAdaptivePatchedData.ideal_phaseCycle_eq_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveSourcePhase.lean)
-/
@[path]
private lemma ideal_phaseCycle_eq_source_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
  (hcross : ∀ i : Fin n, kwComplexCross (polygon.edgeVector i) (polygon.edgeVector (i + 1)) ≠ 0) :
-- imply
  kwVectorPhaseCycle (List.ofFn (kwRawEdge patch.idealVertex)) = kwVectorPhaseCycle polygon.edgeList := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.ideal_phaseCycle_eq_source patch hcoords hcross


-- created on 2026-10-23
