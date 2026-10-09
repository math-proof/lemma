import sympy.Basic
import Mathlib


@[path]
private lemma main
  {x : ℤ}
-- given
  (h₀ : x % 3 = 1)
  (h₁ : x ∈ ({-2, -1, 0, 1, 2} : Finset ℤ)) :
-- imply
  x ∈ ({-2, 1} : Finset ℤ) := by
-- proof
  fin_cases h₁ <;> simp_all


-- created on 2018-11-19
-- updated on 2023-05-12
