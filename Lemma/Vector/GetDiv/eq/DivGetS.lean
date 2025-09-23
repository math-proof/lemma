import Lemma.Vector.Div.eq.Map2
open Vector


@[main]
private lemma fin
  [Div α]
-- given
  (a b : List.Vector α n)
  (i : Fin n) :
-- imply
  (a / b).get i = a.get i / b.get i := by
-- proof
  rw [Div.eq.Map2]
  rw [List.Vector.get_map₂]


@[main]
private lemma main
  [Div α]
-- given
  (a b : List.Vector α n)
  (i : Fin n) :
-- imply
  (a / b)[i] = a[i] / b[i] := by
-- proof
  apply fin


-- created on 2025-09-23
