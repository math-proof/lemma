import Lemma.List.EqCons_Tail.of.GtLength_0
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetMatmul.as.MatmulCastS_Get.of.EqLengthS.GtLength_0
import Lemma.Tensor.GetResize_0.as.Get.of.GtLength_0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.SEqMatmulS.of.SEq.SEq
import sympy.tensor.tensor
open List Tensor
set_option maxHeartbeats 4000000


@[main, fin, cast, cast.fin]
private lemma main
  [Mul α] [Add α] [Zero α]
  {s s' : List ℕ}
-- given
  (h_s : s.length > 0)
  (h_len : s.length = s'.length)
  (X : Tensor α (s ++ [m, k]))
  (Y : Tensor α (s' ++ [k, n]))
  (i : Fin (s[0] ⊓ s'[0])) :
-- imply
  let iX : Fin s[0] := ⟨i.1, by grind⟩
  let iY : Fin s'[0] := ⟨i.1, by grind⟩
  have h_s_eq : s = s[0] :: s.tail := (EqCons_Tail.of.GtLength_0 h_s).symm
  have h_s' : s'.length > 0 := h_len ▸ h_s
  have h_s'_eq : s' = s'[0] :: s'.tail := (EqCons_Tail.of.GtLength_0 h_s').symm
  have h_X : s ++ [m, k] = (s[0] :: s.tail) ++ [m, k] := by
    simpa using congrArg (· ++ [m, k]) h_s_eq
  have h_Y : s' ++ [k, n] = (s'[0] :: s'.tail) ++ [k, n] := by
    simpa using congrArg (· ++ [k, n]) h_s'_eq
  let X' := cast (congrArg (Tensor α) h_X) X
  let Y' := cast (congrArg (Tensor α) h_Y) Y
  have h_i : i < (X.matmul Y h_len).length := by
    rw [Length.eq.Get_0.of.GtLength_0 (by grind)]
    simp [broadcast_shape]
    grind
  (X.matmul Y h_len)[i]'h_i ≃ X'[iX].matmul Y'[iY] (by simp; grind) := by
-- proof
  intros iX iY h_s_eq h_s' h_s'_eq h_X h_Y X' Y' h_i
  have h_cast_i : Fin (s[0] ⊔ s'[0]) := ⟨i, by grind⟩
  have h_matmul_get := GetMatmul.as.MatmulCastS_Get.of.EqLengthS.GtLength_0 h_s h_len X Y h_cast_i
  simp only [X', Y'] at h_matmul_get ⊢
  simp only [GetElem.getElem]
  apply h_matmul_get.trans
  apply SEqMatmulS.of.SEq.SEq (by simp; grind)
  ·
    have h_resize := GetResize_0.as.Get.of.GtLength_0 h_s h_s' X iX
    simp only [GetElem.getElem] at h_resize ⊢
    apply h_resize.trans
    rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin (by grind) h_X X iX]
    rfl
  ·
    have h_resize := GetResize_0.as.Get.of.GtLength_0 h_s' h_s Y iY
    simp only [GetElem.getElem] at h_resize ⊢
    apply h_resize.trans
    rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin (by grind) h_Y Y iY]
    rfl
