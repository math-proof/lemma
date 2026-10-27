import Mathlib.Analysis.Calculus.Deriv.Add
import Initialize.Tactic.Attr.Basic


/--
Policy-gradient score of a finite action distribution has mean zero:
∑ ∂θ p_i(θ) = 0 whenever p(θ) stays on the simplex.
-/
@[path]
private lemma main
  {p : ℝ → ι → ℝ} [Fintype ι]
  {θ₀ : ℝ}
-- given
  (h₀ : ∀ θ, ∑ i, p θ i = 1)
  (h₁ : ∀ i, Differentiable ℝ (fun θ => p θ i)) :
-- imply
  ∑ i, deriv (fun θ => p θ i) θ₀ = 0 := by
-- proof
  have hsum : HasDerivAt (fun θ => ∑ i, p θ i) (∑ i, deriv (fun θ => p θ i) θ₀) θ₀ :=
    HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (h₁ i θ₀).hasDerivAt
  rw [show (fun θ => ∑ i, p θ i) = fun _ => 1 from funext h₀] at hsum
  apply hsum.deriv.symm.trans (hasDerivAt_const θ₀ (1 : ℝ)).deriv


-- created on 2023-04-25
-- updated on 2026-10-26
