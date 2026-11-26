import Mathlib.Algebra.Order.Floor.Ring
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma pigeonhole
  {k n : ℕ}
  {x : ℕ → ℕ}
-- given
  (hk : k > 0)
  (h : ∑ i < k, x i = n) :
-- imply
  ∃ i < k, (x i : ℤ) ≥ ⌈(n : ℝ) / k⌉ := by
-- proof
  simp only [Nat.Iio_eq_range] at h
  by_contra hc
  simp only [not_exists, not_and, not_le] at hc
  have hlt : ∀ i < k, (x i : ℝ) < (n : ℝ) / k := fun i hi => by
    have := hc i hi
    rw [Int.lt_ceil] at this
    exact_mod_cast this
  have := Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr (ne_of_gt hk)) (fun i hi => hlt i (Finset.mem_range.mp hi))
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hk
  have e : (k : ℝ) * ((n : ℝ) / k) = n := by field_simp
  have hs : ((Finset.range k).sum (fun i => (x i : ℝ))) = n := by exact_mod_cast h
  linarith


-- created on 2022-07-06
-- updated on 2026-11-26
