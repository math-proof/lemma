/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Polynomial/RootBound.lean -/

-- Author: @toskua, Avocado

import Mathlib.Algebra.Polynomial.Monic
import Theorem.Algebra.Polynomial.RootBound
import Lemma.Polynomial.RootBound


namespace Polynomial

/-- The standard absolute value on `ℝ` lies over itself. -/
instance absLiesOverSelf :
    AbsoluteValue.LiesOver (AbsoluteValue.abs : AbsoluteValue ℝ ℝ)
      AbsoluteValue.abs where
  under_eq := by
    ext x
    rfl

end Polynomial
