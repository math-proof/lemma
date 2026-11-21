import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Theorem.Vector.GetDiv.eq.DivGetS
import Lemma.Vector.GetCast.eq.Get.of.Eq
open Vector


/--
| attributes | lemma |
| :---: | :---: |
| path | Vector.DivCastS.as.Div.of.Eq |
| cast | Vector.DivCastS.eq.Cast_Div.of.Eq |
-/
@[path, cast]
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
-- updated on 2026-11-20
