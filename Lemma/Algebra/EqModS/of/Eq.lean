import Lemma.Basic


@[main]
private lemma main
  [Mod α]
  {x y : α}
-- given
  (h : x = y)
  (d : α) :
-- imply
  x % d = y % d := by
-- proof
  rw [h]


-- created on 2025-07-06
