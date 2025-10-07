import sympy.Basic


@[main]
private lemma main
  {p q : Prop}
-- given
  (h₀ : p → q)
  (h₁ : p) :
-- imply
  q :=
-- proof
  h₀ h₁


-- created on 2025-04-05
-- updated on 2025-04-12
