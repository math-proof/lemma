import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b x : α}
-- given
  (h₀ : b ≠ x)
  (h₁ : a = x) :
-- imply
  b ≠ a := by
-- proof
  rw [h₁]
  exact h₀


-- created on 2020-02-04
