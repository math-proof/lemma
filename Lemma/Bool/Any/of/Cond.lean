import sympy.Basic


@[path]
private lemma main
-- given
  (h : r)
  (a : α) :
-- imply
  ∃ _ : α, r := by
-- proof
  exists a


@[path]
private lemma ufn
  {p : α → Prop}
-- given
  (h : p e) :
-- imply
  ∃ e, p e := by
-- proof
  use e


-- created on 2018-12-02
