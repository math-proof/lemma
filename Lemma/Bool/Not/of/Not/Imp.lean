import sympy.Basic


@[main]
private lemma main
-- given
  (h₀ : p → q)
  (h₁ : ¬q) :
-- imply
  ¬p :=
-- proof
  fun p => h₁ (h₀ p)


-- created on 2024-07-01
-- updated on 2025-04-14
