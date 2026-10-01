import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {f h : ℕ → ℝ} :
-- imply
  ∏ i ∈ Finset.range n, (f i - h i) = (∏ i ∈ Finset.range n, -(f i - h i)) * (-1) ^ n := by
-- proof
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, ih, pow_succ]
    ring


-- created on 2026-09-27
