import Lemma.Vector.EqGetRange
open Vector


@[main, fin]
private lemma main
  {N : ℕ}
-- given
  (v : List.Vector α N)
  (s : Slice) :
-- imply
  v.getSlice s = (List.Vector.range (s.length N)).map fun i => v[(List.Vector.indices s N)[i]] := by
-- proof
  unfold List.Vector.getSlice
  ext i
  simp [GetElem.getElem, EqGetRange.fin, List.Vector.length]


-- created on 2026-08-07
