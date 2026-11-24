import Lemma.Bool.Imp.is.OrNot


@[path]
private lemma main
  {p q : Prop}
-- given
  (h : ¬p) :
-- imply
  p → q := by
-- proof
  intro hp
  exact absurd hp h




-- created on 2019-06-30
-- updated on 2026-11-24
