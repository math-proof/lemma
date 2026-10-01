import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {f g : ℕ → ℝ} :
-- imply
  ∑ k ∈ Finset.range (n + 1), f k * g k =
    f 0 * ∑ k ∈ Finset.range (n + 1), g k + ∑ k ∈ Finset.range n, (f (k + 1) - f k) * ∑ i ∈ Finset.Ico (k + 1) (n + 1), g i := by
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
  have e : ∀ k ∈ Finset.range n, (f (k + 1) - f k) * ∑ i ∈ Finset.Ico (k + 1) (n + 1), g i =
      (f (k + 1) - f k) * ∑ i ∈ Finset.range (n + 1), g i - (f (k + 1) - f k) * ∑ i ∈ Finset.range (k + 1), g i := by
    intro k hk
    rw [Finset.sum_Ico_eq_sub _ (by have := Finset.mem_range.mp hk; omega)]
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_range_sub, A n]
  ring


-- created on 2023-06-02
