import sympy.Basic


@[main]
private lemma main
  {p : α → Prop}
  {g : β → α}
  {e : β}
-- given
  (h : p (g e)) :
-- imply
  ∃ x, p x := by
-- proof
  use g e


-- created on 2018-05-02
