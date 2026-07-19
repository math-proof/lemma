import Lemma.List.EqCons_Tail.of.GtLength_0
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetMatmul.as.MatmulCastS_Get.of.Eq.EqLengthS.GtLength_0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.SEqMatmulS.of.SEq.SEq
open List Tensor
set_option maxHeartbeats 4000000


@[main, fin, cast, cast.fin]
private lemma main
  [Mul α] [Add α] [Zero α]
  {s s' : List ℕ}
-- given
  (h_s : s.length > 0)
  (h_len : s.length = s'.length)
  (h_0 : s[0] = s'[0])
  (X : Tensor α (s ++ [m, k]))
  (Y : Tensor α (s' ++ [k, n]))
  (i : Fin s[0]) :
-- imply
  let i' : Fin s'[0] := ⟨i.1, by rw [← h_0]; exact i.2⟩
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
  (X.matmul Y h_len)[i]'h_i ≃ X'[i].matmul Y'[i'] (by simp; grind) := by
-- proof
  intros i' h_s_eq h_s' h_s'_eq h_X h_Y X' Y' h_i
  have h_matmul := GetMatmul.as.MatmulCastS_Get.of.Eq.EqLengthS.GtLength_0.fin h_s h_len h_0 X Y i
  simp only [X', Y'] at h_matmul ⊢
  apply h_matmul.trans
  simp only [GetElem.getElem]
  apply SEqMatmulS.of.SEq.SEq (by simp; grind)
  ·
    rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin (by grind) h_X X i]
    rfl
  ·
    rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin (by grind) h_Y Y i']
    rfl


-- created on 2026-07-19
