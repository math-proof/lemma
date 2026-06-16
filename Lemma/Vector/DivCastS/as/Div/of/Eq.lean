import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Vector.GetDiv.eq.DivGetS
import Lemma.Vector.GetCast.eq.Get.of.Eq
open Vector


@[main, cast]
private lemma main
  [Div α]
-- given
  (h : n = n')
  (a b : List.Vector α n) :
-- imply
  have h := (congrArg (List.Vector α) h)
  cast h a / cast h b ≃ a / b := by
-- proof
  intro h
  apply Vector.SEq.of.All_EqGetS.Eq.fin (by aesop)
  intro i
  rw [GetDiv.eq.DivGetS.fin]
  repeat rw [GetCast.eq.Get.of.Eq.fin (by assumption)]
  rw [GetDiv.eq.DivGetS.fin]


-- created on 2025-10-08
