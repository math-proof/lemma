import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.KacWardPolygonPhaseInduction
open StatMech StatMech.FrontierA


/--
[KWFiniteSimplePolygon.phaseCycle_eq_neg_one_of_cleanChordCompatibility](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonPhaseInduction.lean)
-/
@[path]
private lemma phaseCycle_eq_neg_one_of_cleanChordCompatibility_eq
-- given
  (hcompat : KWCleanChordPhaseCompatibility) :
-- imply
  ∀ {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n), kwVectorPhaseCycle polygon.edgeList = -1 := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.phaseCycle_eq_neg_one_of_cleanChordCompatibility hcompat


-- created on 2026-10-23
