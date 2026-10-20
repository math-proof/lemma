import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.ContinuedFractions.LagrangePeriodic
open MetaMathlibExt


/--
[continuedFractionEventuallyPeriodic_of_isRealQuadraticIrrational](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean)
-/
@[path]
private lemma continuedFractionEventuallyPeriodic_of_isRealQuadraticIrrational_eq
  {x : ℝ}
-- given
  (h : IsRealQuadraticIrrational x) :
-- imply
  ContinuedFractionEventuallyPeriodic x := by
-- proof
  apply MetaMathlibExt.continuedFractionEventuallyPeriodic_of_isRealQuadraticIrrational x h


-- created on 2026-10-20
