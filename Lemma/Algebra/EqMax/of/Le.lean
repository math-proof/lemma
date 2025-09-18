import Lemma.Basic


@[main]
private lemma main
  [LinearOrder α]
  {a b : α}
-- given
  (h : a ≤ b) :
-- imply
  a ⊔ b = b := by
-- proof
  simp [h]


-- created on 2025-06-07
