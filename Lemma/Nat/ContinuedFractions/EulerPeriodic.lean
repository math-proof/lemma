import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.ContinuedFractions.EulerPeriodic
open MetaMathlibExt


/--
[isRealQuadraticIrrational_of_continuedFractionEventuallyPeriodic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/EulerPeriodic.lean)
-/
@[path]
private lemma isRealQuadraticIrrational_of_continuedFractionEventuallyPeriodic_eq
  {x : ℝ}
-- given
  (h : ContinuedFractionEventuallyPeriodic x) :
-- imply
  IsRealQuadraticIrrational x := by
-- proof
  apply MetaMathlibExt.isRealQuadraticIrrational_of_continuedFractionEventuallyPeriodic x h

/--
[continuedFractionEventuallyPeriodic_iff_isRealQuadraticIrrational](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/EulerPeriodic.lean)
-/
@[path]
private lemma continuedFractionEventuallyPeriodic_iff_isRealQuadraticIrrational_eq
  {x : ℝ} :
-- imply
  ContinuedFractionEventuallyPeriodic x ↔ IsRealQuadraticIrrational x := by
-- proof
  apply MetaMathlibExt.continuedFractionEventuallyPeriodic_iff_isRealQuadraticIrrational x


-- created on 2026-10-20
