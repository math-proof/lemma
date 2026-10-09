import sympy.Basic


@[path]
private lemma main
  {x y a : α}
-- given
  (h₀ : x = y)
  (h₁ : y ≠ a) :
-- imply
  x ≠ a := by
-- proof
  rw [h₀]
  exact h₁


-- created on 2020-02-11
