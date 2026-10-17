import Mathlib.Algebra.BigOperators.Ring.Finset
import sympy.Basic


@[path]
private lemma main
  {m : ℕ}
  (x : ℕ → ℕ → ℝ) :
-- imply
  ∏ i ∈ Finset.range m, ∏ j ∈ Finset.range 5, x i j
    = ∏ i ∈ Finset.range m, (x i 0 * x i 1 * x i 2 * x i 3 * x i 4) := by
-- proof
  refine Finset.prod_congr rfl ?_
  intro i _
  simp [Finset.prod_range_succ, mul_assoc]


-- created on 2026-10-11
-- updated on 2026-10-17
