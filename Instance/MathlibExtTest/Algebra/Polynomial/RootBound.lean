/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Polynomial/RootBound.lean -/

-- Author: @toskua, Avocado

module

public import Mathlib.Algebra.Polynomial.Monic
public import Theorem.Algebra.Polynomial.RootBound
public import Theorem.Polynomial.RootBound

@[expose] public section

namespace Polynomial

/-- The standard absolute value on `ℝ` lies over itself. -/
instance absLiesOverSelf :
    AbsoluteValue.LiesOver (AbsoluteValue.abs : AbsoluteValue ℝ ℝ)
      AbsoluteValue.abs where
  under_eq := by
    ext x
    rfl

end Polynomial
