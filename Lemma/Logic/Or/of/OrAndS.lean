import sympy.Basic


@[main]
private lemma main
  {R : α → β → Prop}
  {x : α}
  {a b : β}
-- given
  (h : R x a ∧ p ∨ R x b ∧ ¬p) :
-- imply
  p ∨ R x b := by
-- proof
  cases h with
  | inl h =>
    exact Or.inl h.right
  | inr h =>
    exact Or.inr h.left


-- created on 2025-01-12
-- updated on 2025-04-11
