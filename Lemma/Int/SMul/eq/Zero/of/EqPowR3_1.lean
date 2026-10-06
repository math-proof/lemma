import Mathlib
import sympy.Basic


/--
[WeierstrassCurve_variableChange_mk_smul_eq_self_of_pow_three_eq_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_variableChange_mk_smul_eq_self_of_pow_three_eq_one.lean)
-/
@[main]
private lemma main
  [CommRing R]
  {u : Rˣ}
  {B : R}
-- given
  (hu : (u : R) ^ 3 = 1) :
-- imply
  (⟨u, 0, 0, 0⟩ : WeierstrassCurve.VariableChange R) • (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve R) =
      ⟨0, 0, 0, 0, B⟩ := by
-- proof
  have h1 : ((u⁻¹ : Rˣ) : R) * (u : R) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h3 : ((u⁻¹ : Rˣ) : R) ^ 3 = 1 := by
    calc ((u⁻¹ : Rˣ) : R) ^ 3 = ((u⁻¹ : Rˣ) : R) ^ 3 * (u : R) ^ 3 := by rw [hu, mul_one]
      _ = (((u⁻¹ : Rˣ) : R) * (u : R)) ^ 3 := by ring
      _ = 1 := by rw [h1, one_pow]
  have h6 : ((u⁻¹ : Rˣ) : R) ^ 6 = 1 := by
    calc ((u⁻¹ : Rˣ) : R) ^ 6 = (((u⁻¹ : Rˣ) : R) ^ 3) ^ 2 := by ring
      _ = 1 := by rw [h3, one_pow]
  refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_ <;>
    simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆]
  · ring
  · ring
  · ring
  · ring
  · linear_combination B * h6


-- created on 2026-10-05
