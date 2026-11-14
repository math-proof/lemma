/-
Authors: Adam Kiezun, Muse Spark 1.3
-/
import Mathlib.RingTheory.LaurentSeries

/-!
# Coefficients of the weight-two theta operator on Laurent series

This file records `ModularCurve.theta_coeff`: the coefficient of
`q * d/dq f` at `k` is `k • f.coeff k`.
-/

set_option autoImplicit false

noncomputable section

open HahnSeries

namespace ModularCurve

/-- The coefficient of `q • f'` at index `k` is `k • f.coeff k`. -/
theorem theta_coeff {R : Type*} [CommRing R] (f : LaurentSeries R) (k : ℤ) :
    ((HahnSeries.single (1 : ℤ) (1 : R) : LaurentSeries R) *
        LaurentSeries.derivative R f).coeff k =
      k • f.coeff k := by
  rw [HahnSeries.coeff_single_mul, one_mul, LaurentSeries.derivative_apply,
    LaurentSeries.hasseDeriv_coeff]
  simp

end ModularCurve

end
