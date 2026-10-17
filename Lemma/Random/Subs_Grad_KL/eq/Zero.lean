import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import sympy.Basic


/--
At a probability vector the parameter derivative of `KL(p θ' ‖ p θ)` vanishes:
the finite-sum score of `θ' ↦ ∑ a, p θ' a * log (p θ' a / p θ a)` is zero.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [Fintype A]
  {p : Θ → A → ℝ}
  {θ : Θ}
-- given
  (h₀ : ∀ θ', ∑ a, p θ' a = 1)
  (h₁ : ∀ a, p θ a > 0)
  (h₂ : ∀ a, DifferentiableAt ℝ (fun θ' => p θ' a) θ) :
-- imply
  fderiv ℝ (fun θ' => ∑ a, p θ' a * Real.log (p θ' a / p θ a)) θ = 0 := by
-- proof
  have h₃ : ∑ a, fderiv ℝ (fun θ' => p θ' a) θ = 0 := by
    have h₄ : HasFDerivAt (fun θ' => ∑ a, p θ' a) (∑ a, fderiv ℝ (fun θ' => p θ' a) θ) θ :=
      HasFDerivAt.fun_sum fun a _ => (h₂ a).hasFDerivAt
    rw [show (fun θ' => ∑ a, p θ' a) = fun _ => (1 : ℝ) from funext h₀] at h₄
    exact h₄.unique (hasFDerivAt_const 1 θ)
  have h₅ : ∀ a, HasFDerivAt (fun θ' => p θ' a * Real.log (p θ' a / p θ a))
      (fderiv ℝ (fun θ' => p θ' a) θ) θ := by
    intro a
    have h₆ : HasFDerivAt (fun θ' => p θ' a / p θ a)
        ((p θ a)⁻¹ • fderiv ℝ (fun θ' => p θ' a) θ) θ := by
      simpa [div_eq_mul_inv, smul_smul, mul_inv_cancel₀ (h₁ a).ne', one_smul] using
        ((h₂ a).hasFDerivAt.mul_const (p θ a)⁻¹)
    have h₇ : HasFDerivAt (fun θ' => Real.log (p θ' a / p θ a))
        ((p θ a)⁻¹ • fderiv ℝ (fun θ' => p θ' a) θ) θ := by
      simpa [div_self (h₁ a).ne', inv_one] using h₆.log (div_ne_zero (h₁ a).ne' (h₁ a).ne')
    have h₈ := (h₂ a).hasFDerivAt.mul h₇
    simp only [div_self (h₁ a).ne', Real.log_one, zero_smul, add_zero, smul_smul,
      mul_inv_cancel₀ (h₁ a).ne', one_smul] at h₈
    convert h₈
  exact (HasFDerivAt.fun_sum fun a _ => h₅ a).fderiv.trans h₃


-- created on 2023-04-20
-- updated on 2026-10-17
