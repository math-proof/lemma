import sympy.Basic


@[main]
private lemma main
  {p q : Prop} :
-- imply
  p ∨ q ↔ (¬p → q) :=
-- proof
  or_iff_not_imp_left


-- created on 2026-09-27
