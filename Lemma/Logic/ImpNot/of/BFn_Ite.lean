import Lemma.Basic


@[main]
private lemma main
  [Decidable p]
  {R : α → β → Prop}
  {x : α}
  {a b : β}
-- given
  (h : R x (if p then
    a
  else
    b)) :
-- imply
  ¬p → R x b := by
-- proof
  intro hp
  simp_all [h, hp]


-- created on 2025-01-12
-- updated on 2025-04-11
