import sympy.concrete.quantifier
import sympy.Basic


@[main]
private lemma main
  {p q : α → Prop}
-- given
  (h : ∀ x, p x → q x) :
-- imply
  ∀ x | p x, q x :=
-- proof
  h


-- created on 2019-09-02
-- updated on 2026-08-28
