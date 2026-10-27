import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Sum
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n h i : ℕ}
  (f : ℕ → ℝ) :
-- imply
  ∑ j ∈ Finset.Ico h n, ∑ k ∈ Finset.Ico h (j + 1), ((i + j - k).choose i : ℝ) * f k
    = ∑ k ∈ Finset.Ico h n, ((n - k + i).choose (i + 1) : ℝ) * f k := by
-- proof
  rw [← Finset.sum_Ico_Ico_comm]
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [← Finset.sum_mul]
  congr 1
  have hkh : h ≤ k := by
    simp only [Finset.mem_Ico] at hk
    exact hk.1
  have hkn : k < n := by
    simp only [Finset.mem_Ico] at hk
    exact hk.2
  have hinner : ∑ j ∈ Finset.Ico k n, ((i + j - k).choose i : ℝ) =
    ∑ t ∈ Finset.range (n - k), ((i + t).choose i : ℝ) := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl ?_
    intro t ht
    simp only [Finset.mem_range] at ht
    have hidx : i + (k + t) - k = i + t := by omega
    rw [hidx]
  rw [hinner]
  have hs := Nat.sum_range_add_choose (n - k - 1) i
  have hcast := congrArg (Nat.cast : ℕ → ℝ) hs
  rw [show n - k - 1 + i + 1 = n - k + i by omega] at hcast
  rw [show n - k = n - k - 1 + 1 by omega]
  rw [show n - k - 1 + 1 + i = n - k + i by omega]
  simpa [Nat.add_comm, Nat.cast_sum] using hcast


-- created on 2023-06-03
-- updated on 2026-10-26
