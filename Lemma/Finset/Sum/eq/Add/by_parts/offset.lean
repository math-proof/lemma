import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import sympy.Basic


@[path]
private lemma main
  {a n : ℕ}
  (f g : ℕ → ℝ)
-- given
  (h₀ : a ≤ n) :
-- imply
  ∑ k ∈ Finset.Ico a (n + 1), f k * g k
    = f n * ∑ k ∈ Finset.Ico a (n + 1), g k
      - ∑ k ∈ Finset.Ico a n, (f (k + 1) - f k) * ∑ j ∈ Finset.Ico a (k + 1), g j := by
-- proof
  induction n, h₀ using Nat.le_induction with
  | base =>
    simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top (Nat.le_succ_of_le hn), ih]
    conv_rhs =>
      enter [1, 2]
      rw [Finset.sum_Ico_succ_top (Nat.le_succ_of_le hn)]
    conv_rhs =>
      enter [2]
      rw [Finset.sum_Ico_succ_top hn]
    ring


-- created on 2026-10-11
-- updated on 2026-10-17
