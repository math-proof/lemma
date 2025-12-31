import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.DataDiv.eq.DivDataS
import Lemma.Tensor.DataExp.eq.ExpData
import Lemma.Vector.Div.eq.Div_Replicate
import Lemma.Bool.EqUFnS.of.Eq
import Lemma.Tensor.DataCast.eq.Cast_Data.of.Eq
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Tensor.GetData.eq.GetDataGet.of.Lt
import Lemma.Tensor.GetRepeat.eq.Cast_Get_Mod_Get.of.Lt_Mul_Get.GtLength_0
import Lemma.Nat.EqMod_1'0
import Lemma.Tensor.EqGetUnsqueeze
import Lemma.Vector.GetSum.eq.SumMapGet
import Lemma.Vector.GetUnflatten.eq.Get_AddMul
import Lemma.List.Prod.eq.MulProdS
open Tensor Vector Bool Nat List


@[main]
private lemma main
  [Exp α]
-- given
  (X : Tensor α [n]) :
-- imply
  X.softmax = ⟨X.data.softmax⟩ := by
-- proof
  let ⟨X⟩ := X
  unfold Tensor.softmax
  unfold List.Vector.softmax
  apply Eq.of.EqDataS
  rw [DataDiv.eq.DivDataS]
  simp [DataExp.eq.ExpData]
  rw [Div.eq.Div_Replicate]
  apply EqUFnS.of.Eq _ (exp X / ·)
  ext i
  simp
  unfold Tensor.keepdim
  simp
  rw [DataCast.eq.Cast_Data.of.Eq (by simp)]
  rw [GetCast.eq.Get.of.Eq.fin (by simp)]
  rw [GetData.eq.GetDataGet.of.Lt.fin (by grind)]
  have := GetRepeat.eq.Cast_Get_Mod_Get.of.Lt_Mul_Get.GtLength_0.fin (by simp) (by simp; omega) (((exp (⟨X⟩ : Tensor α [n])).sum 0).unsqueeze 0) (i := i) (n := n)
  simp at this
  simp [this]
  simp [EqMod_1'0]
  have := EqGetUnsqueeze.fin ((exp (⟨X⟩ : Tensor α [n])).sum 0)
  simp at this
  simp [this]
  unfold Tensor.sum
  simp [DataExp.eq.ExpData]
  unfold List.Vector.splitAt
  have h_eq := Prod.eq.MulProdS [n] 1
  have := GetSum.eq.SumMapGet.val (cast (congrArg (List.Vector α) h_eq) (exp X)).unflatten ⟨0, by simp⟩
  simp at this
  rw [this]
  apply congrArg
  ext i
  simp
  simp only [GetElem.getElem]
  rw [GetUnflatten.eq.Get_AddMul.fin]
  simp
  rw [GetCast.eq.Get.of.Eq.fin (by simp)]


-- created on 2025-10-11
