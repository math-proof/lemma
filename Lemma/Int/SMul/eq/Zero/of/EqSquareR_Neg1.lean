import Mathlib
import sympy.Basic


/--
[WeierstrassCurve_variableChange_mk_smul_eq_self_of_sq_eq_neg_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_variableChange_mk_smul_eq_self_of_sq_eq_neg_one.lean)
-/
@[main]
private lemma main
  [CommRing R]
  {u : Rˣ}
  {A : R}
-- given
  (hu : (u : R) ^ 2 = -1) :
-- imply
  (⟨u, 0, 0, 0⟩ : WeierstrassCurve.VariableChange R) • (⟨0, 0, 0, A, 0⟩ : WeierstrassCurve R) =
      ⟨0, 0, 0, A, 0⟩ := by
-- proof
  have h1 : ((u⁻¹ : Rˣ) : R) * (u : R) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hu4 : (u : R) ^ 4 = 1 := by
    calc (u : R) ^ 4 = ((u : R) ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hu]; ring
  have h4 : ((u⁻¹ : Rˣ) : R) ^ 4 = 1 := by
    calc ((u⁻¹ : Rˣ) : R) ^ 4 = ((u⁻¹ : Rˣ) : R) ^ 4 * (u : R) ^ 4 := by rw [hu4, mul_one]
      _ = (((u⁻¹ : Rˣ) : R) * (u : R)) ^ 4 := by ring
      _ = 1 := by rw [h1, one_pow]
  refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_ <;>
    simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆]
  · ring
  · ring
  · ring
  · linear_combination A * h4
  · ring


-- created on 2026-10-05
