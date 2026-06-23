import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Vector


@[main, comm 1, cast]
private lemma main
-- given
  (h : n = n')
  (v : List.Vector α n)
  (f : α → β) :
-- imply
  (cast (congrArg (List.Vector α) h) v).map f ≃ v.map f := by
-- proof
  symm
  apply SEq.of.All_EqGetS.Eq.fin h
  simp [GetCast.eq.Get.of.Eq.fin h]


-- created on 2025-11-11
