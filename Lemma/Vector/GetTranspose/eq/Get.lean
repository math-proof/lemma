import Lemma.Vector.EqGetRange.of.Lt
open Vector


@[main]
private lemma main
-- given
  (v : List.Vector (List.Vector α n) m)
  (i : Fin m)
  (j : Fin n) :
-- imply
  v.transpose[j.val, i.val] = v[i.val, j.val] := by
-- proof
  unfold List.Vector.transpose
  simp [EqGetRange.of.Lt]


@[main]
private lemma fin
-- given
  (v : List.Vector (List.Vector α n) m)
  (i : Fin m)
  (j : Fin n) :
-- imply
  (v.transpose.get j).get i = (v.get i).get j := by
-- proof
  apply main


-- created on 2025-06-15
