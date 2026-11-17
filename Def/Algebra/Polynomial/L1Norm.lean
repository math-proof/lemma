module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Basic.Real.Basic

@[expose] public section

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
