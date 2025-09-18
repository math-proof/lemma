import Lemma.Basic


@[main]
private lemma main
  [Field α]
  {b : α}
-- given
  (h : b ≠ 0)
  (a : α) :
-- imply
  a / b * b = a := by
-- proof
  simp [h]


-- created on 2025-03-30
