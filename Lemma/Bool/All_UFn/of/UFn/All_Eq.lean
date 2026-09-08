import Lemma.Bool.UFn.of.UFn.Eq
import sympy.concrete.quantifier
open Bool


@[main]
private lemma main
  {a b : α → β}
  {p : α → β → Prop}
  {r : α → Prop}
-- given
  (h₀ : ∀ x | r x, a x = b x)
  (h₁ : ∀ x | r x, p x (a x)) :
-- imply
  ∀ x | r x, p x (b x) := by
-- proof
  intro x hx
  apply UFn.of.UFn.Eq (h₀ x hx) (h₁ x hx)


-- created on 2019-01-06
-- updated on 2026-09-08
