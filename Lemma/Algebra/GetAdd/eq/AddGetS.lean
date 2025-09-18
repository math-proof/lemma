import stdlib.List.Vector.Basic
import Lemma.Basic


@[main]
private lemma main
  [Add α]
-- given
  (a b : List.Vector α n)
  (i : Fin n) :
-- imply
  (a + b)[i] = a[i] + b[i] := by
-- proof
  conv in a + b =>
    simp [HAdd.hAdd]
  simp [Add.add]
  simp [GetElem.getElem]


@[main]
private lemma fin
  [Add α]
-- given
  (a b : List.Vector α n)
  (i : Fin n) :
-- imply
  (a + b).get i = a.get i + b.get i := by
-- proof
  apply main


-- created on 2025-07-14
