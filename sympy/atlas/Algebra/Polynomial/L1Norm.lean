/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/L1Norm.lean -/

import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Data.Real.Basic

/-!
# L1 norm of a polynomial

This file defines the sum of the absolute values of a polynomial's coefficients.
-/

namespace Polynomial

variable {K : Type*} [Semiring K]

/-- The L1 norm of a polynomial with respect to an absolute value. -/
noncomputable def l1Norm (v : AbsoluteValue K ℝ) (p : Polynomial K) : ℝ :=
  p.sum fun _ a ↦ v a
end Polynomial
