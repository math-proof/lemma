import stdlib.List.Vector
import Lemma.Basic


@[main]
private lemma main
  [Zero α]
  {a : List.Vector α n}
-- given
  (h_i : i < n)
  (h : a = 0) :
-- imply
  a[i] = 0 := by
-- proof
  rw [h]
  apply List.Vector.get_replicate


-- created on 2025-09-04
