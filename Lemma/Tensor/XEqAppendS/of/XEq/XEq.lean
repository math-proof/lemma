import Lemma.Tensor.GetAppend.eq.Get.of.Lt
import Lemma.Tensor.GetAppend.eq.Get_Sub.of.GtAdd.Ge
import Lemma.Tensor.XEq.is.All_XEqGetS
open Tensor


@[main]
private lemma main
  [XEq α]
  {A A' : Tensor α (n :: s)}
  {B B' : Tensor α (m :: s)}
-- given
  (hA : A ≈ A')
  (hB : B ≈ B') :
-- imply
  A ++ B ≈ A' ++ B' := by
-- proof
  apply XEq.of.All_XEqGetS
  intro i
  if hi : (i : ℕ) < n then
    erw [GetAppend.eq.Get.of.Lt hi]
    erw [GetAppend.eq.Get.of.Lt hi]
    apply All_XEqGetS.of.XEq hA ⟨i, hi⟩
  else
    erw [GetAppend.eq.Get_Sub.of.GtAdd.Ge (by grind) (by grind)]
    erw [GetAppend.eq.Get_Sub.of.GtAdd.Ge (by grind) (by grind)]
    apply All_XEqGetS.of.XEq hB ⟨(i : ℕ) - n, by grind⟩


-- created on 2026-08-19
