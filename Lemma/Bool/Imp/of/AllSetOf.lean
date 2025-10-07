import sympy.concrete.quantifier
import sympy.Basic


@[main]
private lemma main
  {p q : α → Prop}

-- given
  (h₀ : ∀ x | p x, q x)
  (x : α):
-- imply
  p x → q x := by
-- proof
  -- Assume p x as the hypothesis h.
  intro h
  -- Apply the universal quantifier h₀ to x and the hypothesis h.
  exact h₀ x h


-- created on 2025-04-20
-- updated on 2025-04-28
