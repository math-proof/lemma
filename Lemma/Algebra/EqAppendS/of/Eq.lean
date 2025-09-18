import Lemma.Basic


@[main]
private lemma left
  {a b : List α}
-- given
  (h : a = b)
  (c : List α) :
-- imply
  c ++ a = c ++ b := by
-- proof
  rw [h]


@[main]
private lemma main
  {a b c : List α}
-- given
  (h : a = b) :
-- imply
  a ++ c = b ++ c := by
-- proof
  rw [h]


-- created on 2025-06-17
