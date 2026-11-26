import Lemma.Real.Grad.eq.Sum
open Real


@[path]
private lemma main
  {n : ℕ}
  {f : ℕ → ℝ → ℝ}
  {x : ℝ}
-- given
  (h : ∀ k < n, DifferentiableAt ℝ (f k) x) :
-- imply
  ∑ k < n, deriv (f k) x = deriv (fun x => ∑ k < n, f k x) x := by
-- proof
  exact (Grad.eq.Sum h).symm


-- created on 2023-04-07
