import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqLength
import Lemma.Tensor.GetAppend.eq.Get.of.Lt
import Lemma.Tensor.GetAppend.eq.Get_Sub.of.GtAdd.Ge
import Lemma.Tensor.GetMap.eq.MapGet
open Tensor


@[main, comm]
private lemma main
  {β : Type*}
-- given
  (A : Tensor α (n :: s))
  (B : Tensor α (m :: s))
  (f : α → β) :
-- imply
  (A ++ B).map f = A.map f ++ B.map f := by
-- proof
  apply Eq.of.All_EqGetS
  intro i
  if hi : (i : ℕ) < n then
    erw [GetMap.eq.MapGet (i := ⟨i, by grind⟩)]
    erw [GetAppend.eq.Get.of.Lt hi]
    erw [GetAppend.eq.Get.of.Lt hi]
    erw [GetMap.eq.MapGet _ f ⟨i, by grind⟩]
    rfl
  else
    erw [GetMap.eq.MapGet (i := ⟨i, by grind⟩)]
    erw [GetAppend.eq.Get_Sub.of.GtAdd.Ge (by omega) i.isLt]
    erw [GetAppend.eq.Get_Sub.of.GtAdd.Ge (by omega) i.isLt]
    erw [GetMap.eq.MapGet _ f ⟨(i : ℕ) - n, by grind⟩]
    rfl


-- created on 2026-08-19
