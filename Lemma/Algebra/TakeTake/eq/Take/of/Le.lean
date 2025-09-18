import Lemma.Basic


@[main]
private lemma main
  {v : List α}
-- given
  (h : i ≤ j) :
-- imply
  (v.take i).take j = v.take i := by
-- proof
  rw [List.take_take]
  simp [h]


-- created on 2025-06-14
