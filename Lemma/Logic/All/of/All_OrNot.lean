import sympy.concrete.quantifier
import sympy.Basic


@[main]
private lemma main
  {p q : α → Prop}
-- given
  (h : ∀ x, ¬q x ∨ p x) :
-- imply
  ∀ x | q x, p x := by
-- proof
  intro x hx
  cases h x with
  | inl h_q =>
    contradiction
  | inr h_p =>
    assumption


-- created on 2025-06-01
