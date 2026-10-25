/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/RootBound.lean -/

import Def.Algebra.Polynomial.L1Norm
import Lemma.Polynomial.L1Norm
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Analysis.Normed.Ring.WithAbs
/-!
# Root bound via the L1 norm

A root of a monic polynomial is strictly bounded by the L1 norm of the
polynomial, provided the absolute value on the root's field restricts to the
absolute value on the coefficient field.
-/


namespace Polynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ)
  [AbsoluteValue.LiesOver w v]
end Polynomial
