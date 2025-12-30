import Lemma.Vector.Div.eq.Map₂
open Vector


@[main]
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


@[main]
private lemma fin
  [Div α]
-- given
  (a b : List.Vector α n)
  (i : Fin n) :
-- imply
  (a / b).get i = a.get i / b.get i :=
-- proof
  main a b i


-- created on 2025-09-23
