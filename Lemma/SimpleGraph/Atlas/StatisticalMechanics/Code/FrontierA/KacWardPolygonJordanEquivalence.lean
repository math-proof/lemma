import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.KacWardPolygonJordanEquivalence
open StatMech StatMech.FrontierA


/--
[kwCleanChordPhaseCompatibility_iff_polygonPhaseSign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonJordanEquivalence.lean)
-/
@[path]
private lemma kwCleanChordPhaseCompatibility_iff_polygonPhaseSign_eq :
-- imply
  KWCleanChordPhaseCompatibility ↔ KWFiniteSimplePolygonPhaseSign := by
-- proof
  apply StatMech.FrontierA.kwCleanChordPhaseCompatibility_iff_polygonPhaseSign

/--
[kwFiniteSimplePolygonPhaseSign_three_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonJordanEquivalence.lean)
-/
@[path]
private lemma kwFiniteSimplePolygonPhaseSign_three_four_eq :
-- imply
  (∀ polygon : KWFiniteSimplePolygon 3, kwVectorPhaseCycle polygon.edgeList = -1) ∧ (∀ polygon : KWFiniteSimplePolygon 4, kwVectorPhaseCycle polygon.edgeList = -1) := by
-- proof
  apply StatMech.FrontierA.kwFiniteSimplePolygonPhaseSign_three_four


-- created on 2026-10-23
