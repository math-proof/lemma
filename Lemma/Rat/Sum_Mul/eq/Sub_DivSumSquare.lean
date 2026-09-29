import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ} :
-- imply
  ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i, x i * x j = (∑ i ∈ Finset.range n, x i) ^ 2 / 2 - (∑ i ∈ Finset.range n, x i ^ 2) / 2 := by
-- proof
  have e : (∑ i ∈ Finset.range n, x i) ^ 2 = 2 * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i, x i * x j + ∑ i ∈ Finset.range n, x i ^ 2 := by
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [Finset.sum_range_succ x, Finset.sum_range_succ (fun i => ∑ j ∈ Finset.range i, x i * x j),
        Finset.sum_range_succ (fun i => x i ^ 2), add_sq, ih, ← Finset.mul_sum]
      ring
  rw [e]
  ring


-- created on 2026-09-27
