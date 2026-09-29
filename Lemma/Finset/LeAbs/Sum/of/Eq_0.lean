import sympy.concrete.expr_with_limits
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {f g : ℕ → ℝ}
-- given
  (h : f (n + 1) = 0) :
-- imply
  |∑ k ∈ Finset.range (n + 1), f k * g k| ≤
    Maxima (↑(Finset.range (n + 1)) : Set ℕ) (fun k => |f (k + 1) - f k|) * ∑ k ∈ Finset.range (n + 1), |∑ i ∈ Finset.range (k + 1), g i| := by
-- proof
  have A : ∀ m, ∑ k ∈ Finset.range (m + 1), f k * g k =
      f m * ∑ i ∈ Finset.range (m + 1), g i - ∑ k ∈ Finset.range m, (f (k + 1) - f k) * ∑ i ∈ Finset.range (k + 1), g i := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun k => (f (k + 1) - f k) * ∑ i ∈ Finset.range (k + 1), g i),
        Finset.sum_range_succ g (m + 1)]
      ring
  have key : ∑ k ∈ Finset.range (n + 1), f k * g k = -∑ k ∈ Finset.range (n + 1), (f (k + 1) - f k) * ∑ i ∈ Finset.range (k + 1), g i := by
    rw [A n, Finset.sum_range_succ (fun k => (f (k + 1) - f k) * ∑ i ∈ Finset.range (k + 1), g i), h]
    ring
  have hM : ∀ k ∈ Finset.range (n + 1), |f (k + 1) - f k| ≤ Maxima (↑(Finset.range (n + 1)) : Set ℕ) (fun k => |f (k + 1) - f k|) :=
    fun k hk => le_csSup ((Finset.finite_toSet _).image _).bddAbove (Set.mem_image_of_mem _ (Finset.mem_coe.mpr hk))
  rw [key, abs_neg, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hM k hk) (abs_nonneg _)


-- created on 2026-09-27
