import Lemma.Bool.SEqCast.of.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.Cons_Append_List.eq.AppendTake_Length
import Lemma.Tensor.Einsum.as.Tensordot.of.EqGetS_SubLength.GeLength_2.GeLength_2
import Lemma.Tensor.Einsum.as.Tensordot.of.GeGetS_SubLength.GeLength_2.GeLength_2
import Lemma.Tensor.Einsum.as.Tensordot.of.LtGetS_SubLength.GeLength_2.GeLength_2
import Lemma.Tensor.EqGetS.of.Eq.GtLength_0
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetMatmul.as.MatmulCastS_Get.of.EqLengthS.GtLength_0
import Lemma.Tensor.GetTensordot.as.MatmulGet.of.GtLength_0
import Lemma.Tensor.GtLengthDot.of.LeLengthS.Ne_Nil
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.SEqGetS.of.SEq.GtLength
import Lemma.Tensor.SEqMatmulS.of.SEq.SEq.Eq.Eq
open Bool List Tensor
set_option maxHeartbeats 40000000


@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h_s : s.length ≥ 2)
  (h_slen : s'.length = s.length)
  (h_nle : n ≤ n')
  (X : Tensor α (n :: s))
  (Y : Tensor α (n' :: s'))
  (i : Fin n) :
-- imply
  (X @ Y)[i]'(GtLengthDot.of.LeLengthS.Ne_Nil (by grind) (by omega) X Y i) ≃ X[i] @ Y[i] := by
-- proof
  simp [GetElem.getElem]
  sorry
  -- match s, s' with
  -- | s₀ :: s₁ :: tl, s'₀ :: s'₁ :: tl' =>
  --   have h_tl : tl'.length = tl.length := by grind
  --   have h_sX : (n :: s₀ :: s₁ :: tl).length ≥ 2 := by grind
  --   have h_sY : (n' :: s'₀ :: s'₁ :: tl').length ≥ 2 := by grind
  --   conv_lhs => simp [Dot.dot]
  --   by_cases h_n_eq : (n :: s₀ :: s₁ :: tl)[(n :: s₀ :: s₁ :: tl).length - 1] = (n' :: s'₀ :: s'₁ :: tl')[(n' :: s'₀ :: s'₁ :: tl').length - 2]
  --   ·
  --     have h_cast := Einsum.eq.Cast_Tensordot.of.EqGetS_SubLength.GeLength_2.GeLength_2 h_sX h_sY h_n_eq X Y
  --     erw [EqGetS.of.Eq.GtLength_0 (by simp [matmul_shape, h_tl]) h_cast ⟨i, by
  --       rw [← Length.eq.Get_0.of.GtLength_0 (by simp [matmul_shape, h_tl])]
  --       exact GtLengthDot.of.LeLengthS.Ne_Nil (by grind) (by omega) X Y i⟩]
  --     rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i, by simp [broadcast_shape, h_tl]; grind⟩) (by grind) (by simp [broadcast_shape, matmul_shape, h_tl])]
  --     apply SEqCast.of.SEq.Eq (by simp [matmul_shape, broadcast_shape, h_tl])
  --     erw [GetTensordot.eq.Cast_MatmulGet.of.GtLength_0.fin (by simp) _ _ ⟨i, by simp⟩]
  --     simp [Tensordot.eq.Cast_Matmul]
  --     rw [Tensordot.eq.Matmul.of.EqLengthS (by grind)]
  --     have h_matmul := GetMatmul.as.MatmulCastS_Get.of.EqLengthS.GtLength_0 (by grind) (by grind) _ _ ⟨i, by
  --       rw [Length.eq.Get_0.of.GtLength_0 (by grind)]
  --       simp [broadcast_shape, h_tl]
  --       grind⟩
  --     simp at h_matmul
  --     apply h_matmul.trans
  --     apply SEqMatmulS.of.SEq.SEq.Eq.Eq (by simp) (by rfl) (by grind)
  --     ·
  --       apply SEqCastS.of.SEq.Eq.Eq (by simp) (by simp [← Cons_Append_List.eq.AppendTake_Length])
  --       erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i, by grind⟩) (by simp) (by simp [← Cons_Append_List.eq.AppendTake_Length])]
  --       apply SEqCast.of.SEq.Eq (by simp [← Cons_Append_List.eq.AppendTake_Length]) (by rfl)
  --       apply SEqGetS.of.SEq.GtLength
  --       apply SEqCast.of.Eq
  --       simp
  --       grind
  --     ·
  --       apply SEqCastS.of.SEq.Eq.Eq (by simp) (by simp [← Cons_Append_List.eq.AppendTake_Length])
  --       erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i, by omega⟩) (by simp) (by simp [← Cons_Append_List.eq.AppendTake_Length])]
  --       apply SEqCast.of.SEq.Eq (by simp [← Cons_Append_List.eq.AppendTake_Length]) (by rfl)
  --       apply SEqGetS.of.SEq.GtLength (by omega)
  --       apply SEqCast.of.Eq
  --       simp
  --       grind
  --   ·
  --     by_cases h_n_lt : (n :: s₀ :: s₁ :: tl)[(n :: s₀ :: s₁ :: tl).length - 1] < (n' :: s'₀ :: s'₁ :: tl')[(n' :: s'₀ :: s'₁ :: tl').length - 2]
  --     ·
  --       have h_cast := Einsum.eq.Cast_Tensordot.of.LtGetS_SubLength.GeLength_2.GeLength_2 h_sX h_sY h_n_lt X Y
  --       erw [EqGetS.of.Eq.GtLength_0 (by simp [matmul_shape, h_tl]) h_cast ⟨i, by
  --         rw [← Length.eq.Get_0.of.GtLength_0 (by simp [matmul_shape, h_tl])]
  --         exact GtLengthDot.of.LeLengthS.Ne_Nil (by grind) (by omega) X Y i⟩]
  --       rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i, by simp [broadcast_shape, h_tl]; grind⟩) (by grind) (by simp [broadcast_shape, matmul_shape, h_tl])]
  --       apply SEqCast.of.SEq.Eq (by simp [matmul_shape, broadcast_shape, h_tl])
  --       erw [GetTensordot.eq.Cast_MatmulGet.of.GtLength_0.fin (by simp) _ _ ⟨i, by simp⟩]
  --       simp [Tensordot.eq.Cast_Matmul]
  --       rw [Tensordot.eq.Matmul.of.EqLengthS (by grind)]
  --       have h_matmul := GetMatmul.as.MatmulCastS_Get.of.EqLengthS.GtLength_0 (by grind) (by grind) _ _ ⟨i, by
  --         rw [Length.eq.Get_0.of.GtLength_0 (by grind)]
  --         simp [broadcast_shape, h_tl]
  --         grind⟩
  --       simp at h_matmul
  --       apply h_matmul.trans
  --       apply SEqMatmulS.of.SEq.SEq.Eq.Eq (by simp) (by rfl) (by grind)
  --       ·
  --         apply SEqCastS.of.SEq.Eq.Eq (by simp) (by simp [← Cons_Append_List.eq.AppendTake_Length])
  --         erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i, by grind⟩) (by simp) (by simp [← Cons_Append_List.eq.AppendTake_Length])]
  --         apply SEqCast.of.SEq.Eq (by simp [← Cons_Append_List.eq.AppendTake_Length]) (by rfl)
  --         apply SEqGetS.of.SEq.GtLength
  --         apply SEqCast.of.Eq
  --         simp
  --         grind
  --       ·
  --         apply SEqCastS.of.SEq.Eq.Eq (by simp) (by simp [← Cons_Append_List.eq.AppendTake_Length])
  --         erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i, by omega⟩) (by simp) (by simp [← Cons_Append_List.eq.AppendTake_Length])]
  --         apply SEqCast.of.SEq.Eq (by simp [← Cons_Append_List.eq.AppendTake_Length]) (by rfl)
  --         apply SEqGetS.of.SEq.GtLength (by omega)
  --         apply SEqCast.of.Eq
  --         simp
  --         grind
  --     ·
  --       have h_n_ge : (n :: s₀ :: s₁ :: tl)[(n :: s₀ :: s₁ :: tl).length - 1] ≥ (n' :: s'₀ :: s'₁ :: tl')[(n' :: s'₀ :: s'₁ :: tl').length - 2] := by omega
  --       have h_cast := Einsum.eq.Cast_Tensordot.of.GeGetS_SubLength.GeLength_2.GeLength_2 h_sX h_sY h_n_ge X Y
  --       erw [EqGetS.of.Eq.GtLength_0 (by simp [matmul_shape, h_tl]) h_cast ⟨i, by
  --         rw [← Length.eq.Get_0.of.GtLength_0 (by simp [matmul_shape, h_tl])]
  --         exact GtLengthDot.of.LeLengthS.Ne_Nil (by grind) (by omega) X Y i⟩]
  --       rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i, by simp [broadcast_shape, h_tl]; grind⟩) (by grind) (by simp [broadcast_shape, matmul_shape, h_tl])]
  --       apply SEqCast.of.SEq.Eq (by simp [matmul_shape, broadcast_shape, h_tl])
  --       erw [GetTensordot.eq.Cast_MatmulGet.of.GtLength_0.fin (by simp) _ _ ⟨i, by simp⟩]
  --       simp [Tensordot.eq.Cast_Matmul]
  --       rw [Tensordot.eq.Matmul.of.EqLengthS (by grind)]
  --       have h_matmul := GetMatmul.as.MatmulCastS_Get.of.EqLengthS.GtLength_0 (by grind) (by grind) _ _ ⟨i, by
  --         rw [Length.eq.Get_0.of.GtLength_0 (by grind)]
  --         simp [broadcast_shape, h_tl]
  --         grind⟩
  --       simp at h_matmul
  --       apply h_matmul.trans
  --       apply SEqMatmulS.of.SEq.SEq.Eq.Eq (by simp) (by rfl) (by grind)
  --       ·
  --         apply SEqCastS.of.SEq.Eq.Eq (by simp) (by simp [← Cons_Append_List.eq.AppendTake_Length])
  --         erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i, by grind⟩) (by simp) (by simp [← Cons_Append_List.eq.AppendTake_Length])]
  --         apply SEqCast.of.SEq.Eq (by simp [← Cons_Append_List.eq.AppendTake_Length]) (by rfl)
  --         apply SEqGetS.of.SEq.GtLength
  --         apply SEqCast.of.Eq
  --         simp
  --         grind
  --       ·
  --         apply SEqCastS.of.SEq.Eq.Eq (by simp) (by simp [← Cons_Append_List.eq.AppendTake_Length])
  --         erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i, by omega⟩) (by simp) (by simp [← Cons_Append_List.eq.AppendTake_Length])]
  --         apply SEqCast.of.SEq.Eq (by simp [← Cons_Append_List.eq.AppendTake_Length]) (by rfl)
  --         apply SEqGetS.of.SEq.GtLength (by omega)
  --         apply SEqCast.of.Eq
  --         simp
  --         grind
  -- | _, _ =>
  --   grind


-- created on 2026-01-04
