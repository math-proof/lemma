import Mathlib.Algebra.BigOperators.Ring.Finset
import sympy.Basic


@[path]
private lemma main
  {a : ℤ}
  (f : ℤ → ℕ)
  (x : ℤ → ℕ → ℝ) :
-- imply
  ∑ i ∈ ({a} : Finset ℤ), ∑ j ∈ Finset.range (f i), x i j
    = ∑ j ∈ Finset.range (f a), x a j := by
-- proof
  simp


-- created on 2026-10-11
-- updated on 2026-10-17
