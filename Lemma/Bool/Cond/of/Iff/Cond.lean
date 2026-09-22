import sympy.Basic


@[main]
private lemma main
  {p q : Prop}
-- given
  (h₀ : p)
  (h₁ : p ↔ q) :
-- imply
  q :=
-- proof
  h₁.mp h₀


-- created on 2019-03-17
