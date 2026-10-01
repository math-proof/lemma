import sympy.Basic


@[main]
private lemma main
  [PartialOrder α]
  {a b : α}
-- given
  (h₀ : a ≤ b)
  (h₁ : a ≥ b) :
-- imply
  a = b :=
-- proof
  le_antisymm h₀ h₁


-- created on 2026-09-27
