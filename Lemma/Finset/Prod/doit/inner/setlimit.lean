import Mathlib.Algebra.BigOperators.Ring.Finset
import sympy.Basic


@[path]
private lemma main
  {m : ℕ}
  (x : ℕ → ℕ → ℝ) :
-- imply
  ∏ i ∈ Finset.range m, ∏ j ∈ ({0, 1, 2, 3} : Finset ℕ), x i j
    = ∏ i ∈ Finset.range m, (x i 0 * x i 1 * x i 2 * x i 3) := by
-- proof
  refine Finset.prod_congr rfl ?_
  intro i _
  simp [mul_assoc]


-- created on 2020-03-03
-- updated on 2026-10-17
