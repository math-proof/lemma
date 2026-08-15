import Lemma.Vector.GetExp.eq.ExpGet
open Vector


@[main]
private lemma main
  [Exp α]
-- given
  (x : List.Vector α n)
  (s : Slice) :
-- imply
  exp (x.getSlice s) = (exp x).getSlice s := by
-- proof
  ext t
  rw [GetExp.eq.ExpGet.fin]
  unfold List.Vector.getSlice
  simp [GetElem.getElem, List.Vector.length]
  rw [← GetExp.eq.ExpGet.fin]


-- created on 2026-08-14
