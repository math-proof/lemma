import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {f : ℕ → ℝ → ℝ}
  {x : ℝ}
-- given
  (h : ∀ k < n, DifferentiableAt ℝ (f k) x) :
-- imply
  deriv (fun x => ∑ k < n, f k x) x = ∑ k < n, deriv (f k) x := by
-- proof
  try simp only [Nat.Iio_eq_range, ← Finset.mem_range] at *
  exact deriv_fun_sum h


-- created on 2020-10-17
