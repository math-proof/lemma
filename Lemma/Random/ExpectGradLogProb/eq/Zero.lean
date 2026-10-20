import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Add
import sympy.Basic


/--
Score identity: if `p θ` is a differentiable probability vector on a finite set and strictly positive at `θ`,
then `∑ a, p θ a • ∇_θ log (p · a) = 0`.
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
  ∑ a, p θ a • fderiv ℝ (fun θ' => Real.log (p θ' a)) θ = 0 := by
-- proof
  simp_rw [fun a => ((h₂ a).hasFDerivAt.log (h₁ a).ne').fderiv, smul_smul, mul_inv_cancel₀ (h₁ _).ne', one_smul]
  have h₃ : HasFDerivAt (fun θ' => ∑ a, p θ' a) (∑ a, fderiv ℝ (fun θ' => p θ' a) θ) θ :=
    HasFDerivAt.fun_sum fun a _ => (h₂ a).hasFDerivAt
  rw [show (fun θ' => ∑ a, p θ' a) = fun _ => (1 : ℝ) from funext h₀] at h₃
  exact h₃.unique (hasFDerivAt_const 1 θ)


-- created on 2023-03-26
-- updated on 2026-10-17
