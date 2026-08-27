import Lemma.Bool.UFn.of.Eq
import Lemma.Nat.EqMod_1'0
import Lemma.Tensor.DataCast.as.Data.of.Eq
import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqGetUnsqueeze_0
import Lemma.Tensor.GetData.eq.GetDataGet.of.Lt
import Lemma.Tensor.GetRepeat_0.as.Get_Mod_Get.of.GtMul_Get.GtLength_0
import Lemma.Tensor.Mul.eq.Mul_GetData_0
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.Head.eq.Get_0
import Lemma.Vector.Mul.eq.Mul_Replicate
import Lemma.Vector.EqGetReplicate
import sympy.tensor.functions
open Bool Nat Tensor Vector


@[main]
private lemma main
  [Mul α]
-- given
  (A : Tensor α [n])
  (X : Tensor α ([n].eraseIdx 0)) :
-- imply
  let den : Tensor α [] := X
  A * X.keepdim = A * den := by
-- proof
  simp
  erw [Mul.eq.Mul_GetData_0]
  apply Eq.of.EqDataS
  rw [DataMul.eq.MulDataS]
  have h_rhs : (A * X.data[0]).data = A.data * List.Vector.replicate [n].prod X.data[0] := calc
    _ = A.data * X.data[0] := by simp [HMul.hMul]
    _ = A.data * List.Vector.replicate [n].prod X.data[0] := Mul.eq.Mul_Replicate (x := A.data) (a := X.data[0])
  erw [h_rhs]
  apply UFn.of.Eq _ (A.data * ·)
  ext i
  simp
  unfold Tensor.keepdim
  simp
  erw [DataCast.eq.Cast_Data.of.Eq (by simp)]
  erw [GetCast.eq.Get.of.Eq.fin (by simp)]
  erw [GetData.eq.GetDataGet.of.Lt.fin (by grind)]
  have := GetRepeat_0.eq.Cast_Get_Mod_Get.of.GtMul_Get.GtLength_0.fin (by simp) (by simp; omega) (X.unsqueeze 0) (i := i) (n := n)
  simp at this
  erw [this]
  simp [EqMod_1'0]
  have := EqGetUnsqueeze_0.fin X
  simp at this
  simp [this]
  erw [EqGetReplicate]
  rfl


-- created on 2026-08-15
