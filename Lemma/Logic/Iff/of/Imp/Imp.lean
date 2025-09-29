import sympy.Basic


@[main]
private lemma main
-- given
  (h₀ : p → q)
  (h₁ : q → p) :
-- imply
  p ↔ q :=
-- proof
  ⟨h₀, h₁⟩


-- created on 2025-04-10
