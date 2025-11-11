import Lemma.Nat.LtVal
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Nat Vector


@[main, comm 1]
private lemma main
-- given
  (h : n = n')
  (v : List.Vector α n)
  (f : α → β) :
-- imply
  v.map f ≃ (cast (congrArg (List.Vector α) h) v).map f := by
-- proof
  apply SEq.of.All_EqGetS.Eq h
  simp [GetCast.eq.Get.of.Eq h]


-- created on 2025-11-11
