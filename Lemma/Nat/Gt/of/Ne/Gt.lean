import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a : ℤ}
-- given
  (h₀ : x ≠ a)
  (h₁ : x > a - 1) :
-- imply
  x > a := by
-- proof
  omega


-- created on 2023-04-13
