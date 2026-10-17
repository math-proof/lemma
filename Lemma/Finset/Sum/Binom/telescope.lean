import Mathlib.Algebra.Group.ForwardDiff
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {x : ℝ}
  (f : ℝ → ℝ) :
-- imply
  ∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ) * (f (x + k + 1) - f (x + k)) =
    ∑ k ∈ Finset.range (n + 2), (-1 : ℝ) ^ (n + 1 - k) * ((n + 1).choose k : ℝ) * f (x + k) := by
-- proof
  have hsum : ∀ m y,
      (fwdDiff (1 : ℝ))^[m] f y =
        ∑ k ∈ Finset.range (m + 1), (-1 : ℝ) ^ (m - k) * (m.choose k : ℝ) * f (y + k) := by
    intro m y
    rw [fwdDiff_iter_eq_sum_shift (1 : ℝ) f m y]
    refine Finset.sum_congr rfl ?_
    intro k _
    simp [zsmul_eq_mul, nsmul_eq_mul]
  have hstep : (fwdDiff (1 : ℝ))^[n + 1] f x =
      (fwdDiff (1 : ℝ))^[n] f (x + 1) - (fwdDiff (1 : ℝ))^[n] f x := by
    rw [Function.iterate_succ_apply']
    simp [fwdDiff]
  have hdiff : ∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ) * (f (x + k + 1) - f (x + k)) =
      ∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ) * f (x + 1 + k) -
        ∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ) * f (x + k) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro k _
    ring_nf
  rw [hdiff, ← hsum n (x + 1), ← hsum n x]
  have hshift : ∀ k, x + 1 + k = x + k + 1 := by
    intro k
    ring
  simp only [hshift] at *
  rw [← hstep, hsum (n + 1) x]


-- created on 2026-10-11
-- updated on 2026-10-17
