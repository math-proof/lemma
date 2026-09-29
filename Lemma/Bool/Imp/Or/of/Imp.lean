import sympy.Basic


@[main]
private lemma main
-- given
  (h : p → q) :
-- imply
  r ∨ p → r ∨ q :=
-- proof
  Or.imp_right h


-- created on 2026-09-27
