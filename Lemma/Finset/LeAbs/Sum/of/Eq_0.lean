import Syntax.Order.ExprWithLimits
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {f g : ℕ → ℝ}
-- given
  (h : f (n + 1) = 0) :
-- imply
  |∑ k < (n + 1), f k * g k| ≤
    Maxima (↑(Finset.range (n + 1)) : Set ℕ) (fun k => |f (k + 1) - f k|) * ∑ k < (n + 1), |∑ i < (k + 1), g i| := by
-- proof
  have A : ∀ m, ∑ k < (m + 1), f k * g k =
      f m * ∑ i < (m + 1), g i - ∑ k < m, (f (k + 1) - f k) * ∑ i < (k + 1), g i := by
    intro m
    induction m with
    | zero => simp [Nat.Iio_eq_range]
    | succ m ih =>
      simp only [Nat.Iio_eq_range] at ih ⊢
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun k => (f (k + 1) - f k) * Finset.sum (Finset.range (k + 1)) g),
        Finset.sum_range_succ g (m + 1)]
      ring
  have key : ∑ k < (n + 1), f k * g k = -∑ k < (n + 1), (f (k + 1) - f k) * ∑ i < (k + 1), g i := by
    simp only [Nat.Iio_eq_range] at A ⊢
    rw [A n, Finset.sum_range_succ (fun k => (f (k + 1) - f k) * Finset.sum (Finset.range (k + 1)) g), h]
    ring
  have hM : ∀ k < (n + 1), |f (k + 1) - f k| ≤ Maxima (↑(Finset.range (n + 1)) : Set ℕ) (fun k => |f (k + 1) - f k|) :=
    fun k hk => le_csSup ((Finset.finite_toSet _).image _).bddAbove (Set.mem_image_of_mem _ (Finset.mem_coe.mpr (Finset.mem_range.mpr hk)))
  rw [key, abs_neg, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hM k (by simpa using hk)) (abs_nonneg _)


-- created on 2023-06-03
