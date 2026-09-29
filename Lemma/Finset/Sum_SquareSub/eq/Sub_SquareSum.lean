import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ} :
-- imply
  ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i, (x i - x j) ^ 2 = n * ∑ i ∈ Finset.range n, x i ^ 2 - (∑ i ∈ Finset.range n, x i) ^ 2 := by
-- proof
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have e : ∑ j ∈ Finset.range n, (x n - x j) ^ 2 =
        n * x n ^ 2 - 2 * x n * ∑ j ∈ Finset.range n, x j + ∑ j ∈ Finset.range n, x j ^ 2 := by
      have : ∀ j ∈ Finset.range n, (x n - x j) ^ 2 = x n ^ 2 - 2 * x n * x j + x j ^ 2 := fun j _ => by ring
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, ← Finset.mul_sum]
    rw [Finset.sum_range_succ (fun i => ∑ j ∈ Finset.range i, (x i - x j) ^ 2), ih, e, Finset.sum_range_succ (fun i => x i ^ 2),
      Finset.sum_range_succ x]
    push_cast
    ring


-- created on 2026-09-27
