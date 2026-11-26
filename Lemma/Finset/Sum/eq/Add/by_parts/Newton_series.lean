import Mathlib.Algebra.BigOperators.Module
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  (f g : ℕ → ℝ) :
-- imply
  ∑ k < (n + 1), f k * g k
    = f n * (∑ k < (n + 1), g k)
      - ∑ k < n,
        (f (k + 1) - f k) * ∑ i < (k + 1), g i := by
-- proof
  simpa [smul_eq_mul, Nat.Iio_eq_range] using Finset.sum_range_by_parts f g (n + 1)


-- created on 2023-06-02
-- updated on 2026-10-26
