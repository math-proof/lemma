import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Tensor.PermuteCast.as.Permute.of.Eq
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.Tensor.Permute__0.eq.Cast
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Vector.Eq.of.Eq_Cast.Eq
import Lemma.Tensor.EqGetS.of.Data.as.FlattenTransposeSplitAt_1
import Lemma.Tensor.PermuteTail.eq.CastRotate.of.LeLength
open Tensor Vector List Bool
set_option maxHeartbeats 2000000


@[main, fin]
private lemma main
-- given
  (X : Tensor α [m, n])
  (i : Fin m)
  (j : Fin n) :
-- imply
  Xᵀ[j, i] = X[i, j] := by
-- proof
  unfold Tensor.T
  simp
  unfold Tensor.transpose
  simp [Permute__0.eq.Cast]
  simp [GetElem.getElem]
  have := Tensor.PermuteCast.eq.Cast_Permute.of.Eq (s' := [m, n].permute 0 0) (by rw [List.EqPermute__0]) X ⟨1, by grind⟩ (-1)
  erw [this]
  have h_s : [m, n] = [m, n].permute 0 0 := by rw [List.EqPermute__0]
  have h_s : [m, n].permute ⟨1, by grind⟩ (-1) = ([m, n].permute 0 0).permute ⟨1, by grind⟩ (-1) := by
    grind
  let X' := (cast (congrArg (Tensor α) h_s) (X.permute ⟨1, by grind⟩ (-1)))
  have h_swap : ([m, n].permute 0 0).permute ⟨1, by grind⟩ (-1) = [m, n].swap 0 1 := by
    simp [List.Swap.eq.PermutePermute.of.Lt.GtLength]
    rfl
  have := GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin
    (s' := ([m, n].swap 0 1))
    (by simp [List.LengthSwap.eq.Length])
    h_swap
    X'
    ⟨j, by simp [List.EqSwap_0'1]⟩
  simp [X'] at this
  erw [this]
  let X' := ((cast (congrArg (Tensor α) h_s) (X.permute 1 (-1))).get j)
  have := GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin
    (s' := ([m, n].swap 0 1).tail)
    (by simp [EqSwap_0'1])
    (by grind)
    X'
    ⟨i, by simp [EqSwap_0'1]⟩
  simp [X'] at this
  erw [this]
  apply EqCast.of.SEq
  rw [EqSwap_0'1] at h_swap
  have := GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin
    (s' := ([m, n].permute 0 0).permute ⟨1, by grind⟩ (-1))
    (by simp)
    (by congr 1)
    (X.permute 1 (-1))
    ⟨j, by grind⟩
  simp at this
  erw [this]
  let X' := (X.permute 1 (-1)).get ⟨j, by grind⟩
  have := GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin
    (s' := (([m, n].permute 0 0).permute ⟨1, by grind⟩ (-1)).tail)
    (by simp)
    (by grind)
    X'
    ⟨i, by simp [h_swap]⟩
  simp [X'] at this
  erw [this]
  apply SEqCast.of.SEq.Eq (by grind)
  apply SEq.of.Eq
  rw [Permute.eq.Ite X]
  simp
  have := GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin
    (s' := [m, n].permute 1 (-1))
    (by simp)
    (by simpa)
    (X.permuteTail 2)
    ⟨j, by grind⟩
  simp at this
  erw [this]
  have := GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin
    (s' := ([m, n].permute 1 (-1)).tail)
    (by simp)
    (by simp; grind)
    ((X.permuteTail 2).get j)
    ⟨i, by grind⟩
  simp at this
  erw [this]
  apply EqCast.of.SEq
  apply SEq.of.Eq
  have := PermuteTail.eq.CastRotate.of.LeLength (n := 2) (X := X) (by simp)
  simp at this
  rw [this]
  have := GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin
    (s' := [m, n].permute 1 (-1))
    (by simp)
    (by simpa)
    (X.rotate 1)
    ⟨j, by grind⟩
  simp at this
  erw [this]
  have := GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin
    (s' := ([m, n].permute 1 (-1)).tail)
    (by simp)
    (by simp; grind)
    ((X.rotate 1).get j)
    ⟨i, by grind⟩
  simp at this
  erw [this]
  apply EqCast.of.SEq
  apply SEq.of.Eq
  unfold Tensor.rotate
  simp
  have h_cast := congrArg (List.Vector α) (MulProdS.eq.ProdAppend ([m, n].drop (1 % [m, n].length)) ([m, n].take (1 % [m, n].length)))
  let data := cast h_cast (X.data.splitAt 1).transpose.flatten
  have h_data : data = cast h_cast (X.data.splitAt 1).transpose.flatten := rfl
  erw [← h_data]
  let X' : Tensor α [n, m] := ⟨data⟩
  have h_X' : X' = ⟨data⟩ := rfl
  erw [← h_X']
  apply EqGetS.of.Data.as.FlattenTransposeSplitAt_1
  simp [X']
  apply Eq.of.Eq_Cast.Eq
  ·
    assumption
  ·
    simp


-- created on 2025-07-13
-- updated on 2025-10-17
