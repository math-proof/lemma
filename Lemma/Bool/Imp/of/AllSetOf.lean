import Syntax.Logic.Quantifier.Part4
import Initialize.Tactic.Attr.Basic


@[path]
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


-- created on 2018-03-25
-- updated on 2026-10-26
