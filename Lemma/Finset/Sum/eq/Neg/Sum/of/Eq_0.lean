import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {f g : ℕ → ℝ}
-- given
  (h : f (n + 1) = 0) :
-- imply
  ∑ k ∈ Finset.range (n + 1), f k * g k = -∑ k ∈ Finset.range (n + 1), (f (k + 1) - f k) * ∑ i ∈ Finset.range (k + 1), g i := by
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
  rw [A n, Finset.sum_range_succ (fun k => (f (k + 1) - f k) * ∑ i ∈ Finset.range (k + 1), g i), h]
  ring


-- created on 2026-09-27
