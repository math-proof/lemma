/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PowerSeries/TaylorFormula.lean -/

-- Author: @toskua, Avocado
/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/

import Mathlib.RingTheory.PowerSeries.Derivative

namespace PowerSeries

/-- Taylor's formula for formal power series: the exponential generating series of the
successive derivatives of `f` is `f(t + u)`.

This is equation (5.32) in Emanuele Munarini, *Combinatorial Identities for the Tricomi
Polynomials*, Journal of Integer Sequences 23 (2020), Article 20.9.4. The variables `t` and `u`
are represented by `MvPowerSeries.X 0` and `MvPowerSeries.X 1`. -/
theorem taylorFormula {R : Type*} [CommRing R] [Algebra ℚ R]
    (f : PowerSeries R) :
    (fun d : Fin 2 →₀ ℕ =>
      ((d 1).factorial : ℚ)⁻¹ •
        coeff (d 0) (d⁄dX^[d 1] f)) =
      MvPowerSeries.subst
        (fun _ : Unit =>
          MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2)) f := by
  funext d
  simp only [← MvPowerSeries.coeff_apply, ← PowerSeries.subst_def]
  rw [coeff_iterate_derivative, coeff_subst_X_zero_add_X_one,
    Nat.ascFactorial_eq_factorial_mul_choose, Nat.cast_mul, mul_assoc,
    ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ,
    inv_smul_smul₀ (by exact_mod_cast (d 1).factorial_ne_zero)]
  have h : (d 0 + d 1).choose (d 1) = (d 0 + d 1).choose (d 0) := by
    rw [add_comm (d 0) (d 1)]
    exact Nat.choose_symm_add
  rw [h]

end PowerSeries
