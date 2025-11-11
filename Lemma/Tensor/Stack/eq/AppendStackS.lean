import Lemma.Tensor.EqLengthStack
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetAppend.eq.Get.of.Lt
import Lemma.Tensor.GetAppend.eq.Get_Sub.of.Lt_Add.Ge
open Tensor


@[main]
private lemma main
  {n : ℕ}
-- given
  (f : ℕ → Tensor α s) :
-- imply
  [i < n + j] f i = [i < n] f i ++ [i < j] f (n + i) := by
-- proof
  have h_length := EqLengthStack f (n + j)
  apply Eq.of.All_EqGetS
  intro i
  rw [EqGetStack]
  if h : i < n then
    simp
    rw [GetAppend.eq.Get.of.Lt h]
    simp [GetElem.getElem]
    rw [EqGetStack.fin]
  else
    simp at h
    simp
    rw [GetAppend.eq.Get_Sub.of.Lt_Add.Ge (by simp_all) (by simp_all)]
    simp [GetElem.getElem]
    simp_all [EqGetStack.fn.fin]


-- created on 2024-12-22
-- updated on 2025-06-14
