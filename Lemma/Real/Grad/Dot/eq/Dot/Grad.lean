import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
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
  have hdot : (fun x' => A ⬝ᵥ f x') = fun x' => ∑ i : Fin n, A i * f x' i := by
    funext x'; simp [dotProduct]
  rw [hdot]
  have hi : ∀ i ∈ (Finset.univ : Finset (Fin n)), DifferentiableAt ℝ (fun x' => A i * f x' i) x := by
    intro i _
    exact DifferentiableAt.const_mul (h i) (A i)
  rw [deriv_fun_sum hi]
  rw [deriv_pi h]
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact deriv_const_mul_field (A i)


-- created on 2026-10-01
