import Lemma.Vector.Sub.eq.Sub_Replicate
open Vector


@[main]
private lemma main
  [SubNegMonoid α]
-- given
  (x : List.Vector α n)
  (a : α)
  (i : Fin n) :
-- imply
  (x - a)[i] = x[i] - a := by
-- proof
  simp [GetElem.getElem]
  rw [Sub.eq.Sub_Replicate]
  rw [GetSub.eq.SubGetS.fin]
  simp


@[main]
private lemma fin
  [SubNegMonoid α]
-- given
  (x : List.Vector α n)
  (a : α)
  (i : Fin n) :
-- imply
  (x - a).get i = x.get i - a :=
-- proof
  main x a i


-- created on 2025-12-03
