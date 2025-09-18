import Lemma.Basic


@[main]
private lemma main
  {n : ℤ}
-- given
  (h : n.toNat = 0) :
-- imply
  n ≤ 0 := by
-- proof
  simp at h
  assumption


-- created on 2025-05-05
