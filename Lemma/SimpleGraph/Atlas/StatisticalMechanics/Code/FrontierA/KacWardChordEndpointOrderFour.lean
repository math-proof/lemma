import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardChordEndpointOrderFour
open StatMech StatMech.FrontierA


/--
[KWFiniteSimplePolygon.phaseCycle_eq_neg_one_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordEndpointOrderFour.lean)
-/
@[path]
private lemma phaseCycle_eq_neg_one_four_eq
  {polygon : KWFiniteSimplePolygon 4} :
-- imply
  kwVectorPhaseCycle polygon.edgeList = -1 := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.phaseCycle_eq_neg_one_four polygon

/--
[KWFiniteSimplePolygon.cleanChordEndpointOrder_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordEndpointOrderFour.lean)
-/
@[path]
private lemma cleanChordEndpointOrder_four_eq
  {polygon : KWFiniteSimplePolygon 4}
  {j : Fin 4}
-- given
  (hj : 2 ≤ j.val)
  (hjupper : j.val + 2 ≤ 4)
  (hclean : polygon.ChordIsClean 0 j) :
-- imply
  polygon.CleanChordEndpointOrder j (by omega) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.cleanChordEndpointOrder_four polygon j hj hjupper hclean


-- created on 2026-10-23
