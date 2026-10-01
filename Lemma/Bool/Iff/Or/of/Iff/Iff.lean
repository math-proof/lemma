import sympy.Basic


@[main]
private lemma main
  {a b x y : Prop}
-- given
  (h₀ : a ↔ b)
  (h₁ : x ↔ y) :
-- imply
  a ∨ x ↔ b ∨ y :=
-- proof
  or_congr h₀ h₁


-- created on 2026-09-27
