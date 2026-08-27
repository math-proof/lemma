import Lemma.List.Swap
open List


@[main]
private lemma main
-- given
  (a b : α)
  (c : List α) :
-- imply
  (a :: b :: c).swap 1 0 = b :: a :: c := by
-- proof
  simp [Swap]


-- created on 2025-06-10
-- updated on 2025-06-16
