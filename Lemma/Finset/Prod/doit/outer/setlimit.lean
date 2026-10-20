import Mathlib.Algebra.BigOperators.Ring.Finset
import sympy.Basic


@[path]
private lemma main
  {a : ℤ}
  (f g : ℤ → ℕ)
  (x : ℤ → ℕ → ℕ → ℝ) :
-- imply
  ∏ i ∈ ({a} : Finset ℤ), ∏ j ∈ Finset.range (f i), ∏ k ∈ Finset.range (g i), x i j k
    = ∏ j ∈ Finset.range (f a), ∏ k ∈ Finset.range (g a), x a j k := by
-- proof
  simp


-- created on 2020-03-05
-- updated on 2026-10-17
