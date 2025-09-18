import stdlib.List
import Lemma.Basic


@[main]
private lemma main
-- given
  (head : List α)
  (tail : List (List α)) :
-- imply
  itertools.product (head :: tail) = head.flatMap (fun h => (itertools.product tail).map (fun t => h :: t)) := by
-- proof
  unfold itertools.product
  simp_all


-- created on 2025-06-13
