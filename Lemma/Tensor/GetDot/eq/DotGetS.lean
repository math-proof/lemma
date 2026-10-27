import Def.Data.Holor.Unsqueeze
import Def.Data.Holor.Repeat
import Notation.Data.Holor.Permute
import Lemma.Nat.EqMod_1'0
import Lemma.Nat.Mul.of.Eq.Eq
import Lemma.Tensor.Dot.eq.SumMul
import Lemma.Tensor.Dot.eq.SumMul__0
import Lemma.Tensor.EqGetUnsqueeze_0
import Lemma.Tensor.Sum.of.Eq
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.Tensor.GetRepeat.as.RepeatGet.of.GtGet_0.GtVal_0
import Lemma.Tensor.GetSum_2.eq.SumGet__0
import Lemma.Tensor.GetUnsqueeze.as.UnsqueezeGet.of.GtGet_0.GtLength_0
import Def.Data.Holor.Sum
open Bool Nat Tensor
set_option maxHeartbeats 625000


private lemma get_mul
  [Mul α]
-- given
  (A B : Tensor α [m, n, k])
  (i : Fin m)
  (j : Fin n) :
-- imply
  ((A * B).get ⟨i, i.isLt⟩).get ⟨j, j.isLt⟩ =
    ((A.get ⟨i, i.isLt⟩).get ⟨j, j.isLt⟩) * ((B.get ⟨i, i.isLt⟩).get ⟨j, j.isLt⟩) := by
-- proof
  have h1 := GetMul.eq.MulGetS A B i
  have h2 := GetMul.eq.MulGetS (A.get ⟨i, i.isLt⟩) (B.get ⟨i, i.isLt⟩) j
  simp [GetElem.getElem] at h1 h2
  exact (congrArg (fun t => t.get ⟨j, j.isLt⟩) h1).trans h2


private lemma factor_a
  [Mul α]
-- given
  (A : Tensor α [m, k])
  (i : Fin m)
  (j : Fin n) :
-- imply
  (((cast (congrArg (Tensor α) (by simp)) ((A.unsqueeze 1).repeat ⟨1, by grind⟩ n) : Tensor α [m, n, k]).get ⟨i, by grind⟩).get ⟨j, by grind⟩) =
    A.get ⟨i, i.isLt⟩ := by
-- proof
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


private lemma factor_b
  [Mul α]
-- given
  (B : Tensor α [k, n])
  (i : Fin m)
  (j : Fin n) :
-- imply
  (((cast (congrArg (Tensor α) (by simp)) ((Bᵀ.unsqueeze 0).repeat ⟨0, by simp⟩ m) : Tensor α [m, n, k]).get ⟨i, by grind⟩).get ⟨j, by grind⟩) =
    Bᵀ.get ⟨j, j.isLt⟩ := by
-- proof
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


/--
tensor version of Matrix.mul_apply
-/
@[path, fin]
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
  have hmul := get_mul
    (cast (congrArg (Tensor α) (by simp)) ((A.unsqueeze 1).repeat ⟨1, by grind⟩ n) : Tensor α [m, n, k])
    (cast (congrArg (Tensor α) (by simp)) ((Bᵀ.unsqueeze 0).repeat ⟨0, by simp⟩ m) : Tensor α [m, n, k])
    ⟨i, i.isLt⟩ ⟨j, j.isLt⟩
  refine hmul.trans ?_
  exact Mul.of.Eq.Eq (factor_a A i j) (factor_b B i j)


-- created on 2025-06-22
-- updated on 2026-10-26
