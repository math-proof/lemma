import stdlib.List.Vector
import Lemma.Basic


@[main]
private lemma main
-- given
  (head : List.Vector α n)
  (tail : List.Vector (List.Vector α n) m) :
-- imply
  ((head ::ᵥ tail).toList.map List.Vector.toList).flatten = head.toList ++ (tail.toList.map List.Vector.toList).flatten := by
-- proof
  cases head
  cases tail
  simp [List.Vector.toList]

-- created on 2025-05-08
