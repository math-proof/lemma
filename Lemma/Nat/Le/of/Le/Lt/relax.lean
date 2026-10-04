import sympy.Basic


@[main]
private lemma main
  {a x b : ℕ}
-- given
  (h₀ : a ≤ x)
  (h₁ : x < b) :
-- imply
  a ≤ b := by
-- proof
  exact h₀.trans (Nat.le_of_lt h₁)


-- created on 2019-11-24
