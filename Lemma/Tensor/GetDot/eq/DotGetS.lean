import Lemma.Bool.SEq.is.Eq
import Lemma.Nat.EqMod_1'0
import Lemma.Nat.Mul.of.Eq.Eq
import Lemma.Tensor.Dot.eq.SumMul
import Lemma.Tensor.Dot.eq.SumMul__0
import Lemma.Tensor.EqGetUnsqueeze_0
import Lemma.Tensor.Sum.of.Eq
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.Tensor.GetRepeat.as.RepeatGet.of.GtGet_0.GtVal_0
import Lemma.Tensor.GetRepeat_0.as.Get_Mod_Get.of.GtMul_Get.GtLength_0
import Lemma.Tensor.GetSum_2.eq.SumGet__0
import Lemma.Tensor.GetUnsqueeze.as.UnsqueezeGet.of.GtGet_0.GtLength_0
import Lemma.Tensor.SEqGetS.of.SEq.GtLength
open Bool Nat Tensor
set_option maxHeartbeats 2500000


/--
tensor version of Matrix.mul_apply
-/
@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (A : Tensor α [m, k])
  (B : Tensor α [k, n])
  (i : Fin m)
  (j : Fin n) :
-- imply
  (A @ B)[i, j] = A[i] @ Bᵀ[j] := by
-- proof
  rw [Dot.eq.SumMul]
  let Ai : Tensor α [k] := A[i]
  let Bj : Tensor α [k] := Bᵀ[j]
  have := Dot.eq.SumMul__0 Ai Bj
  simp [Ai, Bj] at this
  erw [this]
  simp [GetElem.getElem]
  erw [GetSum_2.eq.SumGet__0.fin]
  apply Sum.of.Eq (i := 0)
  conv_lhs => erw [GetMul.eq.MulGetS.fin]
  conv_lhs => erw [GetMul.eq.MulGetS.fin]
  apply Mul.of.Eq.Eq
  ·
    apply Eq.of.SEq
    apply (SEqGetS.of.SEq.GtLength (by grind)
      (GetCast.as.Get.of.Eq.GtLength_0.right.fin
        (s' := [m, n, k]) (by grind) (by simp)
        ((A.unsqueeze 1).repeat ⟨1, by grind⟩ n)
        ⟨i, by grind⟩)).trans
    apply (SEqGetS.of.SEq.GtLength (by grind)
      (GetRepeat.as.RepeatGet.of.GtGet_0.GtVal_0.fin
        (by grind) (by grind)
        (A.unsqueeze 1) n)).trans
    apply (GetRepeat_0.as.Get_Mod_Get.of.GtMul_Get.GtLength_0.fin
      (s := [1, k]) (by simp) (by grind)
      ((A.unsqueeze 1).get ⟨i, by grind⟩)).trans
    simp [EqMod_1'0]
    apply (SEqGetS.of.SEq.GtLength (i := 0) (by grind)
      (GetUnsqueeze.as.UnsqueezeGet.of.GtGet_0.GtLength_0
        (s := [m, k]) (by simp) i.isLt A 0)).trans
    apply SEq.of.Eq
    apply EqGetUnsqueeze_0
  ·
    apply Eq.of.SEq
    apply SEqGetS.of.SEq.GtLength (by grind)
    apply (GetCast.as.Get.of.Eq.GtLength_0.right.fin
      (s' := [m, n, k]) (by grind) (by simp)
      ((Bᵀ.unsqueeze 0).repeat ⟨0, by simp⟩ m)
      ⟨i, by grind⟩).trans
    apply (GetRepeat_0.as.Get_Mod_Get.of.GtMul_Get.GtLength_0.fin
      (s := [1, n, k]) (by simp) (by grind)
      (Bᵀ.unsqueeze 0)).trans
    simp [EqMod_1'0]
    apply SEq.of.Eq
    apply EqGetUnsqueeze_0


-- created on 2025-06-22
-- updated on 2026-08-27
