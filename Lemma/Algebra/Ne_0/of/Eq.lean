import Lemma.Basic


@[main]
private lemma main
  [Zero α]
  [NeZero (b : α)]
  {a : α}
-- given
  (h : a = b) :
-- imply
  a ≠ 0 := by
-- proof
  rw [h]
  apply NeZero.ne


-- created on 2025-07-20
