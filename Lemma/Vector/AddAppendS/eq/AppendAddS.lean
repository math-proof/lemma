import Lemma.Vector.GetAdd.eq.AddGetS
import Lemma.Vector.GetAppend.eq.Get.of.Lt
import Lemma.Vector.GetAppend.eq.Get_Sub.of.Lt_Add.Ge
open Vector


@[main]
private lemma main
  [Add α]
-- given
  (a c : List.Vector α n)
  (b d : List.Vector α m) :
-- imply
  (a ++ b) + (c ++ d) = (a + c) ++ (b + d) := by
-- proof
  ext i
  if h_i : n > i then
    rw [GetAdd.eq.AddGetS.fin]
    rw [GetAppend.eq.Get.of.Lt.fin h_i]
    rw [GetAppend.eq.Get.of.Lt.fin h_i]
    rw [GetAppend.eq.Get.of.Lt.fin h_i]
    rw [GetAdd.eq.AddGetS.fin]
  else
    rw [GetAdd.eq.AddGetS.fin]
    rw [GetAppend.eq.Get_Sub.of.Lt_Add.Ge.fin (by grind) (by grind)]
    rw [GetAppend.eq.Get_Sub.of.Lt_Add.Ge.fin (by grind) (by grind)]
    rw [GetAppend.eq.Get_Sub.of.Lt_Add.Ge.fin (by grind) (by grind)]
    rw [GetAdd.eq.AddGetS.fin]


-- created on 2026-08-23
