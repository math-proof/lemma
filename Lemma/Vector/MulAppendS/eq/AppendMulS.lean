import Lemma.Vector.GetMul.eq.MulGetS
import Lemma.Vector.GetAppend.eq.Get.of.Lt
import Lemma.Vector.GetAppend.eq.Get_Sub.of.Lt_Add.Ge
open Vector


@[main]
private lemma main
  [Mul α]
-- given
  (a c : List.Vector α n)
  (b d : List.Vector α m) :
-- imply
  (a ++ b) * (c ++ d) = (a * c) ++ (b * d) := by
-- proof
  ext i
  if h_i : n > i then
    rw [GetMul.eq.MulGetS.fin]
    repeat rw [GetAppend.eq.Get.of.Lt.fin h_i]
    rw [GetMul.eq.MulGetS.fin]
  else
    rw [GetMul.eq.MulGetS.fin]
    repeat rw [GetAppend.eq.Get_Sub.of.Lt_Add.Ge.fin (by grind) (by grind)]
    rw [GetMul.eq.MulGetS.fin]


-- created on 2026-08-23
