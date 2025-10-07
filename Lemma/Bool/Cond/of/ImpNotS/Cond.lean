import sympy.Basic


@[main]
private lemma main
  {a b : Prop}
-- given
  (h₀ : b)
  (h₁ : ¬a → ¬b) :
-- imply
  a :=
-- proof
  -- modus tollens reverse
  Function.mtr h₁ h₀


-- created on 2025-04-13
