import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [PartialOrder α]
  {a b x : α}
-- given
  (h₀ : b ≤ x)
  (h₁ : x ∈ Icc a b) :
-- imply
  x = b :=
-- proof
  le_antisymm h₁.right h₀


-- created on 2026-10-03
