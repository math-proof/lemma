import Lemma.Vector.GetCast.eq.Get.of.Eq
open Vector


@[main, fin]
private lemma main
-- given
  (h_i : i < n)
  (h : n = n')
  (v : List.Vector α n)
  (f : α → β) :
-- imply
  (cast (congrArg (List.Vector β) h) (v.map f))[i] = f v[i] := by
-- proof
  simp [GetElem.getElem]
  simp [GetCast.eq.Get.of.Eq.fin h]


-- created on 2025-07-15
