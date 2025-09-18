import Lemma.Basic


@[main]
private lemma main
-- given
  (head : α)
  (tail : List α) :
-- imply
  (head :: tail).length > 0 := by
-- proof
  simp


-- created on 2025-07-24
