import sympy.Basic


@[path]
private lemma main
  {b x a : Prop}
-- given
  (h₀ : b ↔ x)
  (h₁ : x ↔ a) :
-- imply
  b ↔ a :=
-- proof
  h₀.trans h₁


-- created on 2019-09-12
