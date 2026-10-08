import sympy.Basic


@[main]
private lemma main
  [AddGroup α]
  {x y a : α} :
-- imply
  x + a = y ↔ x = y - a := by
-- proof
  exact eq_sub_iff_add_eq.symm


-- created on 2026-10-03
