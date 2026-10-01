import Mathlib.Analysis.Calculus.Deriv.MeanValue
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {f : ℕ → ℝ → ℝ}
  {x : ℝ}
-- given
  (h : ∀ k ∈ Finset.range n, DifferentiableAt ℝ (f k) x) :
-- imply
  deriv (fun x => ∑ k ∈ Finset.range n, f k x) x = ∑ k ∈ Finset.range n, deriv (f k) x := by
-- proof
  exact deriv_fun_sum h


-- created on 2020-10-17
