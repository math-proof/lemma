import sympy.Basic


@[main]
private lemma right
  {p q r : Prop}
-- given
  (h₀ : p → q)
  (h₁ : r → p) :
-- imply
  r → q :=
-- proof
  fun h : r =>
    h₀ (h₁ h)


@[main]
private lemma main
  {p q r : Prop}
-- given
  (h₀ : p → q)
  (h₁ : q → r) :
-- imply
  p → r :=
-- proof
  fun h : p =>
    h₁ (h₀ h)


-- created on 2024-07-01
-- updated on 2025-04-10
