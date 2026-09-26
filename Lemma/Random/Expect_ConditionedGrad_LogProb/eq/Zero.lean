import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Add
import sympy.Basic


/--
Expected grad-log-prob lemma on a finite outcome space: for a differentiable, positive family of
probability vectors `p θ` (e.g. the policy `π_θ(· | s)`),
`𝔼_{a ∼ p θ}[∇_θ log p θ a] = ∑ a, p θ a • ∇_θ log p θ a = 0`.
-/
@[main]
private lemma main
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [Fintype A]
  {p : Θ → A → ℝ}
  {θ : Θ}
-- given
  (h₀ : ∀ θ', ∑ a, p θ' a = 1)
  (h₁ : ∀ a, p θ a > 0)
  (h₂ : ∀ a, DifferentiableAt ℝ (fun θ' => p θ' a) θ) :
-- imply
  ∑ a, p θ a • fderiv ℝ (fun θ' => Real.log (p θ' a)) θ = 0 := by
-- proof
  have h₃ : ∀ a, fderiv ℝ (fun θ' => Real.log (p θ' a)) θ =
      (p θ a)⁻¹ • fderiv ℝ (fun θ' => p θ' a) θ :=
    fun a => ((h₂ a).hasFDerivAt.log (h₁ a).ne').fderiv
  simp_rw [h₃, smul_smul]
  have h₄ : ∀ a, p θ a * (p θ a)⁻¹ = 1 := fun a => mul_inv_cancel₀ (h₁ a).ne'
  simp only [h₄, one_smul]
  have h₅ : HasFDerivAt (fun θ' => ∑ a, p θ' a) (∑ a, fderiv ℝ (fun θ' => p θ' a) θ) θ :=
    HasFDerivAt.fun_sum fun a _ => (h₂ a).hasFDerivAt
  have h₆ : (fun θ' => ∑ a, p θ' a) = fun _ => (1 : ℝ) := funext h₀
  rw [h₆] at h₅
  exact h₅.unique (hasFDerivAt_const 1 θ)


-- created on 2026-09-26
