import Mathlib
import Initialize.Tactic.Attr.Basic


namespace PowerSeries

/--
[taylorFormula](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PowerSeries/TaylorFormula.lean)
-/
@[path]
lemma taylorFormula
  [CommRing R] [Algebra ℚ R]
  {f : PowerSeries R} :
-- imply
  (fun d : Fin 2 →₀ ℕ =>
    ((d 1).factorial : ℚ)⁻¹ •
    coeff (d 0) (d⁄dX^[d 1] f)) =
    MvPowerSeries.subst
    (fun _ : Unit =>
    MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2)) f := by
-- proof
  funext d
  simp only [← MvPowerSeries.coeff_apply, ← PowerSeries.subst_def]
  rw [coeff_iterate_derivative, coeff_subst_X_zero_add_X_one,
    Nat.ascFactorial_eq_factorial_mul_choose, Nat.cast_mul, mul_assoc,
    ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ,
    inv_smul_smul₀ (by exact_mod_cast (d 1).factorial_ne_zero)]
  have h : (d 0 + d 1).choose (d 1) = (d 0 + d 1).choose (d 0) := by
    rwa [add_comm (d 0) (d 1)]
  rw [h]

end PowerSeries


-- created on 2026-10-20
-- updated on 2026-10-26
