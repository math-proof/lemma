import Lemma.Bool.UFn.of.Eq
import Lemma.Nat.EqMod_1'0
import Lemma.Tensor.DataCast.as.Data.of.Eq
import Lemma.Tensor.DataDiv.eq.DivDataS
import Lemma.Tensor.Div.eq.Div_GetData_0
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqGetUnsqueeze_0
import Lemma.Tensor.GetData.eq.GetDataGet.of.Lt
import Lemma.Tensor.GetRepeat_0.as.Get_Mod_Get.of.GtMul_Get.GtLength_0
import Lemma.Vector.Div.eq.Div_Replicate
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.Head.eq.Get_0
import sympy.tensor.functions
open Bool Nat Tensor Vector


@[main]
private lemma main
  [Div α] [Add α] [Zero α]
-- given
  (X : Tensor α [n]) :
-- imply
  let den : Tensor α [] := X.sum 0
  X / ((X.sum 0).keepdim) = X / den := by
-- proof
  simp
  rw [Div.eq.Div_GetData_0]
  apply Eq.of.EqDataS
  rw [DataDiv.eq.DivDataS]
  have h_rhs : (X / (X.sum 0).data[0]).data = X.data / List.Vector.replicate [n].prod (X.sum 0).data[0] := calc
    _ = X.data / (X.sum 0).data[0] := by simp [HDiv.hDiv]
    _ = X.data / List.Vector.replicate [n].prod (X.sum 0).data[0] := Div.eq.Div_Replicate (v := X.data) (d := (X.sum 0).data[0])
  erw [h_rhs]
  apply UFn.of.Eq _ (X.data / ·)
  ext i
  simp
  unfold Tensor.keepdim
  simp
  erw [DataCast.eq.Cast_Data.of.Eq (by simp)]
  erw [GetCast.eq.Get.of.Eq.fin (by simp)]
  erw [GetData.eq.GetDataGet.of.Lt.fin (by grind)]
  have := GetRepeat_0.eq.Cast_Get_Mod_Get.of.GtMul_Get.GtLength_0.fin (by simp) (by simp; omega) ((X.sum 0).unsqueeze 0) (i := i) (n := n)
  simp at this
  erw [this]
  simp [EqMod_1'0]
  have := EqGetUnsqueeze_0.fin (X.sum 0)
  simp at this
  simp [this, Head.eq.Get_0]
  rfl


-- created on 2026-07-25
