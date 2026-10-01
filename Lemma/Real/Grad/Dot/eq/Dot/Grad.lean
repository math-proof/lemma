import Mathlib.Analysis.Calculus.Deriv.Add
import sympy.Basic
open BigOperators


@[main]
private lemma main
  {n : ℕ}
  {f : ℝ → (Fin n → ℝ)}
  {A : Fin n → ℝ}
  {x : ℝ}
-- given
  (h : ∀ i : Fin n, DifferentiableAt ℝ (fun x' => f x' i) x) :
-- imply
  deriv (fun x' => A ⬝ᵥ f x') x = A ⬝ᵥ deriv f x := by
-- proof
  have hdot : ∀ (x' : ℝ), A ⬝ᵥ f x' = ∑ i : Fin n, A i * f x' i := by
    intro x'; simp [dotProduct]
  rw [funext hdot]
  have hi : ∀ i ∈ (Finset.univ : Finset (Fin n)), DifferentiableAt ℝ (fun x' => A i * f x' i) x := by
    intro i _
    have hfd := DifferentiableAt.hasDerivAt (h i)
    exact (hfd.const_mul (A i)).differentiableAt
  rw [deriv_sum hi]
  congr with i
  rw [deriv_mul_const_field (A i)]
  rw [deriv_pi h]
  rfl


-- created on 2026-10-01
