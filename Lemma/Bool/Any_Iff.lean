import sympy.Basic


@[main]
private lemma main
  {R : α → β → Prop} :
-- imply
  ∃ R' : β → α → Prop, (∀ (a : α) (b : β), R a b ↔ R' b a) := by
-- proof
  use fun b a => R a b
  intro a b
  simp


-- created on 2025-04-12
