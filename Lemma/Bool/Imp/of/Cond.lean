import Lemma.Bool.Imp.is.OrNot


@[main]
private lemma main
  {p q : Prop}
-- given
  (h : p) :
-- imply
  q → p := by
-- proof
  simp [h]


@[main]
private lemma invert.given
  {p q : Prop}
-- given
  (h : ¬p) :
-- imply
  p → q := by
-- proof
  intro hp
  exact absurd hp h


@[main]
private lemma unbounded
  {p c : α → Prop}
  {x : α}
-- given
  (h : p x) :
-- imply
  c x → p x := by
-- proof
  intro _
  exact h


-- created on 2019-06-30
-- updated on 2026-09-27
