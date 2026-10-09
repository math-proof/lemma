import sympy.Basic


@[path]
private lemma main
  {p q : Prop} :
-- imply
  p ∨ q ↔ (¬p → q) :=
-- proof
  or_iff_not_imp_left


-- created on 2020-02-21
