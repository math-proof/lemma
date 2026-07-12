import Lemma.Vector.EqGet0_0
import Lemma.Vector.GetAppend.eq.Get.of.Lt
import Lemma.Vector.GetAppend.eq.Get_Sub.of.Lt_Add.Ge
open Vector


@[main]
private lemma main
  [Zero α]
-- given
  (n m : ℕ) :
-- imply
  (0 : List.Vector α n) ++ (0 : List.Vector α m) = (0 : List.Vector α (n + m)) := by
-- proof
  ext i
  if h_i : n > i then
    rw [GetAppend.eq.Get.of.Lt.fin h_i]
    simp [EqGet0_0.fin]
  else
    rw [GetAppend.eq.Get_Sub.of.Lt_Add.Ge.fin (by grind) (by grind)]
    simp [EqGet0_0.fin]


-- created on 2026-07-12
