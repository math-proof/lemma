import sympy.Basic


@[main]
private lemma main
  {a b : α}
  {p : α → Prop}
-- given
  (h₀ : a = b)
  (h₁ : p a) :
-- imply
  p b := by
-- proof
  exact h₀ ▸ h₁


-- created on 2025-01-12
