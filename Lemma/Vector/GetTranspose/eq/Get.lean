import Lemma.Vector.EqGetRange.of.Lt
open Vector


@[main, fin, val]
private lemma main
-- given
  (v : List.Vector (List.Vector α n) m)
  (i : Fin m)
  (j : Fin n) :
-- imply
  v.transpose[j, i] = v[i, j] := by
-- proof
  unfold List.Vector.transpose
  simp [EqGetRange.of.Lt]


-- created on 2025-06-15
