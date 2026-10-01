import sympy.Basic


@[main]
private lemma given
  {p q r : Prop}
-- given
  (h₀ : ¬p → r)
  (h₁ : q → r) :
-- imply
  (p → q) → r := by
-- proof
  intro h
  by_cases hp : p
  ·
    exact h₁ (h hp)
  ·
    exact h₀ hp


-- created on 2026-09-27
