import Lemma.Vector.Div.eq.Map₂
open Vector


@[main, fin]
private lemma main
  [Div α]
-- given
  (a b : List.Vector α n)
  (i : Fin n) :
-- imply
  (a / b)[i] = a[i] / b[i] := by
-- proof
  simp [GetElem.getElem]
  rw [Div.eq.Map₂]
  rw [List.Vector.get_map₂]


-- created on 2025-09-23
