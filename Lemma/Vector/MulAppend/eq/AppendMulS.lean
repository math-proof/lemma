import Lemma.Vector.GetMul.eq.MulGet
import Lemma.Vector.GetAppend.eq.Get.of.Lt
import Lemma.Vector.GetAppend.eq.Get_Sub.of.Lt_Add.Ge
open Vector


@[main]
private lemma main
  [Mul α]
-- given
  (a : List.Vector α n)
  (b : List.Vector α m)
  (c : α) :
-- imply
  (a ++ b) * c = (a * c) ++ (b * c) := by
-- proof
  ext i
  if h_i : n > i then
    rw [GetMul.eq.MulGet.fin]
    repeat rw [GetAppend.eq.Get.of.Lt.fin h_i]
    rw [GetMul.eq.MulGet.fin]
  else
    rw [GetMul.eq.MulGet.fin]
    repeat rw [GetAppend.eq.Get_Sub.of.Lt_Add.Ge.fin (by grind) (by grind)]
    rw [GetMul.eq.MulGet.fin]


-- created on 2026-08-23
