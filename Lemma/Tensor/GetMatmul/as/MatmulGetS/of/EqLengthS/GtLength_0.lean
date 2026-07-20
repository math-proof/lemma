import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.EqCons_Tail.of.GtLength_0
import Lemma.List.TailSet_0.eq.Tail
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetMatmul.as.MatmulCastS_Get.of.EqLengthS.GtLength_0
import Lemma.Tensor.GetResize_0.as.Get.of.GtLength_0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.SEqGetS.of.SEq.GtLength
import Lemma.Tensor.SEqMatmulS.of.SEq.SEq
import Lemma.Tensor.SEqResizeS.of.SEq.EqValS.Eq
-- this is added to avoid a bug in the Lean 4 compiler that environment saying: already contains 'List.getElem?_zipWith.match_1.congr_eq_1._sparseCasesOn_2'
import Lemma.Tensor.GtLengthDot.of.LeLengthS.Ne_Nil
open Bool List Tensor
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
  have h_X : s ++ [m, k] = (s[0] :: s.tail) ++ [m, k] := by
    simpa using congrArg (· ++ [m, k]) (EqCons_Tail.of.GtLength_0 h_s).symm
  have h_Y : s' ++ [k, n] = (s'[0] :: s'.tail) ++ [k, n] := by
    simpa using congrArg (· ++ [k, n]) (EqCons_Tail.of.GtLength_0 (h_len ▸ h_s)).symm
  let X' := cast (congrArg (Tensor α) h_X) X
  let Y' := cast (congrArg (Tensor α) h_Y) Y
  have h_i : i < (X.matmul Y h_len).length := by
    rw [Length.eq.Get_0.of.GtLength_0 (by grind)]
    simp [broadcast_shape]
    grind
  have : i < s[0] := by grind
  have : i < s'[0] := by grind
  (X.matmul Y h_len)[i]'h_i ≃ X'[i].matmul Y'[i] (by simp; grind) := by
-- proof
  intros h_X h_Y X' Y' h_i iX iY
  simp only [GetElem.getElem]
  have h_matmul_get := GetMatmul.as.MatmulCastS_Get.of.EqLengthS.GtLength_0 h_s h_len X Y ⟨i, by grind⟩
  apply h_matmul_get.trans
  apply SEqMatmulS.of.SEq.SEq (by simp; grind)
  ·
    rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin (by grind) h_X X ⟨i, by grind⟩]
    apply SEqCastS.of.SEq.Eq.Eq (by simp [TailSet_0.eq.Tail]; grind) (by grind)
    have h_resize := GetResize_0.as.Get.of.GtLength_0.fin (by grind) X ⟨i, by grind⟩ s'[0]
    simp at h_resize ⊢
    symm
    apply h_resize.symm.trans
    apply SEqGetS.of.SEq.GtLength (by grind)
    apply SEqResizeS.of.SEq.EqValS.Eq (by grind) (by grind)
    rfl
  ·
    rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin (by grind) h_Y Y ⟨i, by grind⟩]
    apply SEqCastS.of.SEq.Eq.Eq (by simp [TailSet_0.eq.Tail]; grind) (by grind)
    have h_resize := GetResize_0.as.Get.of.GtLength_0 (by grind) Y ⟨i, by grind⟩ s[0]
    simp at h_resize
    symm
    apply h_resize.symm.trans
    apply SEqGetS.of.SEq.GtLength (by grind)
    apply SEqResizeS.of.SEq.EqValS.Eq (by grind) (by grind)
    rfl


-- created on 2026-07-20
