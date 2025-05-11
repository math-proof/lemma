import Lemma.Basic


@[main]
private lemma left
  [Add α]
  [LE α]
  [AddLeftReflectLE α]
  {a b d : α}
-- given
  (h : d + a ≤ d + b) :
-- imply
  a ≤ b :=
-- proof
  le_of_add_le_add_left h


@[main]
private lemma main
  [Add α]
  [LE α]
  [AddRightReflectLE α]
  {a b d : α}
-- given
  (h : a + d ≤ b + d) :
-- imply
  a ≤ b :=
-- proof
  le_of_add_le_add_right h


-- created on 2025-05-10
