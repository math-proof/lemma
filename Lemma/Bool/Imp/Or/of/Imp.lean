import sympy.Basic


@[path]
private lemma main
-- given
  (h : p → q) :
-- imply
  r ∨ p → r ∨ q :=
-- proof
  Or.imp_right h


-- created on 2019-10-05
