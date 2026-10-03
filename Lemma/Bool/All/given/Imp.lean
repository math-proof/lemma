import sympy.concrete.quantifier
import sympy.Basic


@[main]
private lemma main
  {p q : α → Prop}
-- given
  (h : ∀ x | p x, q x)
  (x : α) :
-- imply
  p x → q x := by
-- proof
  intro hpx
  exact h x hpx


-- created on 2026-10-03
