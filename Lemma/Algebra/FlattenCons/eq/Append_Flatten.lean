import Lemma.Basic


@[main]
private lemma main
-- given
  (head : List α)
  (tail : List (List α)) :
-- imply
  (head :: tail).flatten = head ++ tail.flatten := by
-- proof
  simp [List.flatten]


-- created on 2025-05-08
