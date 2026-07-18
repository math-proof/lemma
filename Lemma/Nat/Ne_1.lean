import sympy.Basic


@[main, subst 0]
private lemma main
  [Zero α]
  [One α]
  [NeZero (1 : α)] :
-- imply
  (0 : α) ≠ 1 :=
-- proof
  zero_ne_one


-- created on 2026-07-12
-- updated on 2026-07-19
