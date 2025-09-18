import stdlib.List.Vector
import Lemma.Basic


@[main]
private lemma main
-- given
  (h : j < n ⊓ N)
  (v : List.Vector α N) :
-- imply
  (v.take n)[j] = v[j] := by
-- proof
  simp [GetElem.getElem]
  split_ifs with h <;>
  ·
    simp [List.Vector.take]
    cases v
    simp [List.Vector.get]


-- created on 2025-05-31
