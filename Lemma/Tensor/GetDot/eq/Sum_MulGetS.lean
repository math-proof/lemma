import Lemma.Algebra.LtVal
import Lemma.Tensor.GetMul.eq.MulGetS.of.Lt_Get_0.GtLength_0
import Lemma.Tensor.GetCast.eq.Cast_Get.of.Eq.Lt_Get_0.GtLength_0
import Lemma.Tensor.GetRepeat.eq.Cast_RepeatGet.of.Lt_Get_0.GtVal_0
import Lemma.Tensor.EqGetRepeatUnsqueeze_0_0.of.Lt
import Lemma.Tensor.GetSum_2.eq.SumGet__0
import Lemma.Tensor.GetRepeat.eq.Cast_Get_Mod_Get_0.of.Lt_Mul_Get_0.GtLength_0
import Lemma.Tensor.LengthUnsqueeze.eq.Length.of.Gt_0
import Lemma.Algebra.EqMod_1'0
import Lemma.Tensor.GetUnsqueeze.eq.Cast_UnsqueezeGet.of.Lt_Get_0.Gt_0.GtLength_0
import Lemma.Tensor.EqGetUnsqueeze_0_0
import Lemma.Tensor.Sum_0.eq.Sum_Get
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.Tensor.GetTranspose.eq.Get
open Algebra Tensor
set_option maxHeartbeats 1000000


/--
tensor version of Matrix.mul_apply
-/
@[main]
private lemma main
  [Mul α]
  [AddCommMonoid α]
-- given
  (A : Tensor α [m, l])
  (B : Tensor α [l, n])
  (i : Fin m)
  (j : Fin n) :
-- imply
  (A @ B)[i, j] = ∑ k : Fin l, A[i, k] * B[k, j] := by
-- proof
  simp [MatMul.dot]
  simp [Tensor.dot]
  have : ∀ X : Tensor α [m, n, l], (X.sum 2)[i][j] = X[i][j].sum 0 := GetSum_2.eq.SumGet__0 (i := i) (j := j)
  simp_all [GetMul.eq.MulGetS.of.Lt_Get_0.GtLength_0 (s := [m, n, l])]
  simp_all [GetMul.eq.MulGetS.of.Lt_Get_0.GtLength_0 (s := [n, l])]
  repeat rw [GetCast.eq.Cast_Get.of.Eq.Lt_Get_0.GtLength_0 (by simp) (by simp) (by simp)]
  simp
  have h_i := LtVal i
  have := GetRepeat.eq.Cast_RepeatGet.of.Lt_Get_0.GtVal_0 (show (⟨1, by simp⟩ : Fin 3) > 0 by simp) h_i (A.unsqueeze 1) n
  simp at this
  simp [this]
  have := EqGetRepeatUnsqueeze_0_0.of.Lt.fin h_i Bᵀ
  simp at this
  simp only [GetElem.getElem]
  rw [this]
  rw [GetCast.eq.Cast_Get.of.Eq.Lt_Get_0.GtLength_0.fin (by simp) (by simp) (by simp)]
  have := GetRepeat.eq.Cast_Get_Mod_Get_0.of.Lt_Mul_Get_0.GtLength_0.fin
    (s := [m, 1, l].tail) (i := j) (n := n)
    (by simp) (by simp)
    ((A.unsqueeze 1).get ⟨i, by simp_all [Tensor.length]⟩)
  simp [EqMod_1'0] at this
  simp [this]
  have := GetUnsqueeze.eq.Cast_UnsqueezeGet.of.Lt_Get_0.Gt_0.GtLength_0
    (s := [m, l]) (d := 1) (i := i)
    (by simp) (by simp) (by simp)
    A
  simp [GetElem.getElem] at this
  rw [this]
  have := EqGetUnsqueeze_0_0.fin (A.get i)
  simp at this
  simp [this]
  rw [Sum_0.eq.Sum_Get.fin]
  simp [GetMul.eq.MulGetS.fin (A := A.get i)]
  simp [GetTranspose.eq.Get.fin B]


-- created on 2025-06-22
-- updated on 2025-07-13
