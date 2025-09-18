import Lemma.Basic


@[main]
private lemma main
-- given
  (head : α)
  (tail : List α) :
-- imply
  head :: tail = [head] ++ tail := by
-- proof
  simp


-- created on 2025-05-17
