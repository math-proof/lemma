import Lemma.Basic


@[main]
private lemma main
  {n : ℕ}
-- given
  (v : List.Vector α n.succ) :
-- imply
  v.head = v.get 0 := by
-- proof
  simp


-- created on 2025-07-11
