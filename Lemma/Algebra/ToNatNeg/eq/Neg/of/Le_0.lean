import Lemma.Basic


@[main]
private lemma main
  {z : ℤ}
-- given
  (h : z ≤ 0) :
-- imply
  (-z).toNat = -z := by
-- proof
  simp [h]


-- created on 2025-07-14
