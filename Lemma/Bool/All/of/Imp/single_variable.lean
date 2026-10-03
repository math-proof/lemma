import sympy.Basic


@[main]
private lemma main
  {α β : Type*}
  {p : α → β → Prop}
  {q : α → β → Prop}
  (y : β)
-- given
  (h : ∀ x z, p x z → q x z) :
-- imply
  ∀ x, p x y → q x y := by
-- proof
  intro x hxy
  exact h x y hxy


-- created on 2026-10-03
