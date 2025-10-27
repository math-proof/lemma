import sympy.Basic


@[main]
private lemma main
-- given
  (h : r)
  (a : α) :
-- imply
  ∃ _ : α, r := by
-- proof
  exists a


@[main]
private lemma ufn
  {p : α → Prop}
-- given
  (h : p e) :
-- imply
  ∃ e, p e := by
-- proof
  use e


-- created on 2024-07-01
