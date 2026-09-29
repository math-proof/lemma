import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given.dilated
  {d l u L U : ℤ}
-- given
  (h₀ : L = d * (l - 1) + 1)
  (h₁ : U = d * (u - 1) + 1) :
-- imply
  d * (l - 1) + d * (u - 1) + 1 = L + U - 1 := by
-- proof
  rw [h₀, h₁]
  ring


-- created on 2026-09-27
