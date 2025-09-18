import stdlib.List
import Lemma.Basic


@[main]
private lemma main
-- given
  (head : List α)
  (tail : List (List α)) :
-- imply
  (itertools.product (head :: tail)).length = head.length * (itertools.product tail).length := by
-- proof
  unfold itertools.product
  simp_all


-- created on 2025-06-13
