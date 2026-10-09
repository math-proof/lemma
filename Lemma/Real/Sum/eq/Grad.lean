import Lemma.Real.Grad.eq.Sum
import sympy.Basic
open Real


@[path]
private lemma main
  {n : ℕ}
  {f : ℕ → ℝ → ℝ}
  {x : ℝ}
-- given
  (h : ∀ k ∈ Finset.range n, DifferentiableAt ℝ (f k) x) :
-- imply
  ∑ k ∈ Finset.range n, deriv (f k) x = deriv (fun x => ∑ k ∈ Finset.range n, f k x) x := by
-- proof
  exact (Grad.eq.Sum h).symm


-- created on 2026-10-01
