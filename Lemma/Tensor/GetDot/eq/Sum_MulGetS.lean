import Lemma.Tensor.RepeatCast.as.Repeat.of.Eq
import Lemma.Tensor.UnsqueezeCast.as.Unsqueeze.of.Eq
import Lemma.Tensor.GetMul.eq.MulGetS.of.Lt_Get_0.GtLength_0
import Lemma.Tensor.GetCast.as.Get.of.Lt_Get_0.Eq.GtLength_0
import Lemma.Tensor.GetRepeat.as.RepeatGet.of.Lt_Get_0.GtVal_0
import Lemma.Tensor.EqGetRepeatUnsqueeze.of.Lt
import Lemma.Tensor.GetSum_2.eq.SumGet__0
import Lemma.Tensor.GetRepeat.as.Get_Mod_Get.of.GtMul_Get.GtLength_0
import Lemma.Tensor.LengthUnsqueeze.eq.Length.of.Gt_0
import Lemma.Nat.EqMod_1'0
import Lemma.Tensor.GetUnsqueeze.as.UnsqueezeGet.of.Lt_Get_0.Gt_0.GtLength_0
import Lemma.Tensor.EqGetUnsqueeze
import Lemma.Tensor.Sum_0.eq.Sum_Get
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.Tensor.GetTranspose.eq.Get
import Lemma.List.EqSwap_0'1
open Tensor Nat List
set_option maxHeartbeats 10000000


private lemma get_mul_m
  [Mul α]
-- given
  (A B : Tensor α [m, n, l])
  (i : Fin m) :
-- imply
  (A * B).get ⟨i, by simp [Length.eq.Get_0.of.GtLength_0]⟩ = A.get ⟨i, by simp [Length.eq.Get_0.of.GtLength_0]⟩ * B.get ⟨i, by simp [Length.eq.Get_0.of.GtLength_0]⟩ := by
-- proof
  apply GetMul.eq.MulGetS.of.Lt_Get_0.GtLength_0.fin
  repeat simp

private lemma get_mul_n
  [Mul α]
-- given
  (A B : Tensor α [n, l])
  (j : Fin n) :
-- imply
  (A * B).get ⟨j, by simp [Length.eq.Get_0.of.GtLength_0]⟩ = A.get ⟨j, by simp [Length.eq.Get_0.of.GtLength_0]⟩ * B.get ⟨j, by simp [Length.eq.Get_0.of.GtLength_0]⟩ := by
-- proof
  apply GetMul.eq.MulGetS.of.Lt_Get_0.GtLength_0.fin
  repeat simp


private lemma repeat_cast
-- given
  (B : Tensor α [l, n]) :
-- imply
  let s := ([l, n].swap ([l, n].length - 2) ([l, n].length - 1)).insertIdx 0 1
  let s' := [1, n, l]
  (cast (congrArg (Tensor α) (show s = s' by simp [s, s', EqSwap_0'1])) (Bᵀ.unsqueeze 0)).repeat m (0 : Fin 3) =
    cast (congrArg (Tensor α) (show s.set 0 (m * s[0]'(by grind)) = s'.set 0 (m * s'[0]'(by grind)) by simp [s, s', EqSwap_0'1])) ((Bᵀ.unsqueeze 0).repeat m (0 : Fin 3)) := by
-- proof
  intro s s'
  have h_s: s = s' := by
    simp [s, s', EqSwap_0'1]
  have := RepeatCast.eq.Cast_Repeat.of.Eq h_s (Bᵀ.unsqueeze 0) m ⟨0, by grind⟩
  simp at this
  assumption

--
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
  simp [Tensor.batch_dot]
  simp [GetElem.getElem]
  erw [GetSum_2.eq.SumGet__0.fin]
  erw [get_mul_m]
  erw [get_mul_n]
  erw [UnsqueezeCast.eq.Cast_Unsqueeze.of.Eq (show [l, n].swap ([l, n].length - 2) ([l, n].length - 1) = [n, l] by simp [EqSwap_0'1])]
  erw [repeat_cast B]

  have h_s : (([l, n].swap ([l, n].length - 2) ([l, n].length - 1)).insertIdx 0 1).set 0 (m * (([l, n].swap ([l, n].length - 2) ([l, n].length - 1)).insertIdx 0 1)[0]) =
    (([n, l].insertIdx 0 1).set 0 (m * ([n, l].insertIdx 0 1)[0])) := by
    simp [EqSwap_0'1]
  have := GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin
    (s' := [m, n, l])
    (by simp)
    (by grind)
    (cast (congrArg (Tensor α) h_s) ((Bᵀ.unsqueeze 0).repeat m ⟨0, by grind⟩))
    ⟨i, by grind⟩
  simp at this
  erw [this]

  -- have := GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin
  --   (s' := [m, n, l])
  --   (by simp)
  --   (by grind)
  --   ((A.unsqueeze 1).repeat n ⟨1, by grind⟩)
  --   ⟨i, by grind⟩
  -- simp at this
  -- erw [this]

  -- have := GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin
  --   (s' := [m, n, l])
  --   (by simp)
  --   (by grind)
  --   ((Bᵀ.unsqueeze 0).repeat m ⟨0, by grind⟩)
  --   ⟨i, by grind⟩
  -- simp at this
  -- erw [this]

  -- have h_i := i.isLt
  -- have := GetRepeat.eq.Cast_RepeatGet.of.Lt_Get_0.GtVal_0.fin (show (⟨1, by simp⟩ : Fin 3) > 0 by simp) h_i (A.unsqueeze 1) n
  -- simp at this
  -- rw [this]

  -- have := EqGetRepeatUnsqueeze.of.Lt.fin h_i Bᵀ
  -- simp at this
  -- rw [this]

  -- have := GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin
  --   (s' := [n, l])
  --   (by simp)
  --   (by grind)
  --   (((A.unsqueeze 1).get i).repeat n ⟨0, by grind⟩)
  --   ⟨j, by grind⟩
  -- simp at this
  -- erw [this]

  -- have := GetRepeat.eq.Cast_Get_Mod_Get.of.GtMul_Get.GtLength_0.fin
  --   (s := [1, l]) (i := j) (n := n)
  --   (by simp) (by simp)
  --   ((A.unsqueeze 1).get ⟨i, by simp_all [Tensor.length]⟩)
  -- simp [EqMod_1'0] at this
  -- simp [this]
  -- have := GetUnsqueeze.eq.Cast_UnsqueezeGet.of.Lt_Get_0.Gt_0.GtLength_0.fin
  --   (s := [m, l]) (d := 1) (i := i)
  --   (by simp) (by simp) (by simp)
  --   A
  -- simp at this
  -- rw [this]
  -- have := EqGetUnsqueeze.fin (A.get i)
  -- simp at this
  -- simp [this]
  -- rw [Sum_0.eq.Sum_Get.fin]
  -- simp [GetMul.eq.MulGetS.fin (A := A.get i)]
  -- simp [GetTranspose.eq.Get.fin B]
  sorry
#check UnsqueezeCast.eq.Cast_Unsqueeze.of.Eq
-- created on 2025-06-22
-- updated on 2025-07-13
