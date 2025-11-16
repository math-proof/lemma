import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.GetGetSlice.eq.Get.of.Lt_Min
import Lemma.List.LengthSlice.eq.Min
import Lemma.Nat.Lt_Min.is.Lt.Lt
open Tensor List Nat


@[main]
private lemma main
  {m : ℕ}
  {X Y : Tensor α (m :: s)}
-- given
  (h : X = Y)
  (n : ℕ) :
-- imply
  X[:n] = Y[:n] := by
-- proof
  apply Eq.of.All_EqGetS
  intro i
  have h_i := i.isLt
  simp [LengthSlice.eq.Min] at h_i
  simp [Tensor.length] at h_i
  have h_i := Lt_Min.of.Lt.Lt h_i.left h_i.right
  simp only [GetElem.getElem]
  have := GetGetSlice.eq.Get.of.Lt_Min.fin X h_i
  have := GetGetSlice.eq.Get.of.Lt_Min.fin Y h_i
  simp_all
  have h_gets := All_EqGetS.of.Eq h
  specialize h_gets ⟨i, by linarith⟩
  simp only [GetElem.getElem] at h_gets
  assumption


-- created on 2025-09-29
