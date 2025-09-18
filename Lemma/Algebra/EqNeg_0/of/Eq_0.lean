import Lemma.Basic


@[main]
private lemma main
  [Ring α]
  {a : α}
-- given
  (h : a = 0) :
-- imply
  -a = 0 := by
-- proof
  rw [h]
  simp


-- created on 2025-04-19
