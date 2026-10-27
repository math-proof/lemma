import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [AddGroup α]
  {x y a : α} :
-- imply
  x + a = y ↔ x = y - a := by
-- proof
  exact eq_sub_iff_add_eq.symm


-- created on 2018-05-16
