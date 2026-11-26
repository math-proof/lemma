import Abbrev.Difference
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {f : ℤ → ℝ}
  {x : ℤ} :
-- imply
  ∑ k < (n + 1), (-1) ^ (n - k) * (n.choose k : ℝ) * f (x + k) = Difference f n x := by
-- proof
  try simp only [Nat.Iio_eq_range] at *
  unfold Difference
  rw [fwdDiff_iter_eq_sum_shift]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [zsmul_eq_mul]


-- created on 2021-11-26
