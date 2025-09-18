import Lemma.Algebra.ValAppend.eq.AppendValS
open Algebra


@[main]
private lemma main
-- given
  (a : List.Vector α n)
  (b : List.Vector α m)
  (i : Fin n) :
-- imply
  (a ++ b)[i] = a[i] := by
-- proof
  simp [GetElem.getElem]
  simp [List.Vector.get]
  simp [ValAppend.eq.AppendValS]


-- created on 2025-05-30
-- updated on 2025-05-31
