import Lemma.Vector.GetAppend.eq.Get.of.Lt
import Lemma.Vector.GetAppend.eq.Get_Sub.of.Lt_Add.Ge
import Lemma.Vector.XEq.is.All_XEqGetS
open Vector


@[main]
private lemma main
  [XEq α]
  {a a' : List.Vector α n}
  {b b' : List.Vector α m}
-- given
  (ha : a ≈ a')
  (hb : b ≈ b') :
-- imply
  a ++ b ≈ a' ++ b' := by
-- proof
  apply XEq.of.All_XEqGetS
  intro i
  if hi : (i : ℕ) < n then
    erw [GetAppend.eq.Get.of.Lt hi]
    erw [GetAppend.eq.Get.of.Lt (a := a') hi]
    exact (All_XEqGetS.of.XEq ha) ⟨i, hi⟩
  else
    have hge : (i : ℕ) ≥ n := Nat.le_of_not_gt hi
    have hlt : (i : ℕ) < n + m := i.isLt
    erw [GetAppend.eq.Get_Sub.of.Lt_Add.Ge hge hlt]
    erw [GetAppend.eq.Get_Sub.of.Lt_Add.Ge (a := a') hge hlt]
    exact (All_XEqGetS.of.XEq hb) ⟨(i : ℕ) - n, by grind⟩


-- created on 2026-08-19
