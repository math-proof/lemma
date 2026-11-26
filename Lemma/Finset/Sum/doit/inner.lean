import Mathlib.Algebra.BigOperators.Ring.Finset
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {m : ℕ}
  (x : ℕ → ℕ → ℝ) :
-- imply
  ∑ i < m, ∑ j < 5, x i j
    = ∑ i < m, (x i 0 + x i 1 + x i 2 + x i 3 + x i 4) := by
-- proof
  try simp only [Nat.Iio_eq_range] at *
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [Finset.sum_range_succ, add_assoc]


-- created on 2026-10-11
-- updated on 2026-10-26
