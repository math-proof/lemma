import sympy.Basic


@[main]
private lemma main
  {b x a : Prop}
-- given
  (h₀ : b ↔ x)
  (h₁ : x ↔ a) :
-- imply
  b ↔ a :=
-- proof
  h₀.trans h₁


-- created on 2026-09-27
