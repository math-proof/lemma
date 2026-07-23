import Lemma.List.SetAppend.eq.Append_Set.of.GtLength
import Lemma.List.Set_0.eq.Cons_Tail.of.GtLength_0
import Lemma.List.TailAppend.eq.AppendTail.of.GtLength_0
import Lemma.List.TailSet_0.eq.Tail
import Lemma.Tensor.GetMatmul.as.MatmulCastS_Get.of.Eq.EqLengthS.GtLength_0
import Lemma.Tensor.GtLength.of.GtLength_0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.Matmul.as.MatmulResizeS.of.EqLengthS.GtLength_0
open List Tensor
set_option maxHeartbeats 1000000


@[main, cast]
private lemma main
  [Mul α] [Add α] [Zero α]
  {s s' : List ℕ}
-- given
  (h : s.length > 0)
  (h_length : s.length = s'.length)
  (X : Tensor α (s ++ [m, n]))
  (Y : Tensor α (s' ++ [n, k]))
  (i : Fin (s[0] ⊔ s'[0])) :
-- imply
  let X' := X.resize ⟨0, by grind⟩ (s[0] ⊔ s'[0])
  let Y' := Y.resize ⟨0, by grind⟩ (s[0] ⊔ s'[0])
  let Xi : Tensor α (s.tail ++ [m, n]) := cast
    (congrArg (Tensor α) (by
      rw [TailSet_0.eq.Tail]
      rw [TailAppend.eq.AppendTail.of.GtLength_0 (by grind)]
    ))
    (X'.get ⟨i, GtLength.of.GtLength_0 (by grind) X' ⟨i, by grind⟩⟩)
  let Yi : Tensor α (s'.tail ++ [n, k]) := cast
    (congrArg (Tensor α) (by
      rw [TailSet_0.eq.Tail]
      rw [TailAppend.eq.AppendTail.of.GtLength_0 (by grind)]
    ))
    (Y'.get ⟨i, GtLength.of.GtLength_0 (by grind) Y' ⟨i, by grind⟩⟩)
  have h_i : i < (X.matmul Y h_length).length := by
    rw [Length.eq.Get_0.of.GtLength_0 (by grind)]
    simp [broadcast_shape]
    grind
  (X.matmul Y (by grind)).get ⟨i, h_i⟩ ≃ Xi.matmul Yi (by simp; grind) := by
-- proof
  intro X' Y' Xi Yi h_i
  let X'' : Tensor α ((s[0] ⊔ s'[0]) :: s.tail ++ [m, n]) := cast (congrArg (Tensor α) (by
    rw [SetAppend.eq.Append_Set.of.GtLength (by grind)]
    congr 1
    simp
    rw [Set_0.eq.Cons_Tail.of.GtLength_0 (by grind)]
  )) X'
  let Y'' : Tensor α ((s[0] ⊔ s'[0]) :: s'.tail ++ [n, k]) := cast (congrArg (Tensor α) (by
    rw [SetAppend.eq.Append_Set.of.GtLength (by grind)]
    congr 1
    simp
    rw [Set_0.eq.Cons_Tail.of.GtLength_0 (by grind)]
  )) Y'
  have := GetMatmul.as.MatmulCastS_Get.of.Eq.EqLengthS.GtLength_0 (by grind) (by grind) (by grind) X'' Y'' i
  simp [X'', Y'', X', Y'] at this
  simp [Xi, Yi, X', Y']
  symm at this
  symm
  erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i, by grind⟩) (by grind) (by rw [List.Set_0.eq.Cons_Tail.of.GtLength_0 (by grind)]; grind)] at this
  erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (s' := s[0] ⊔ s'[0] :: s'.tail ++ [n, k]) (i := ⟨i, by grind⟩) (by grind) (by rw [List.Set_0.eq.Cons_Tail.of.GtLength_0 (by grind)]; grind)] at this
  apply this.trans
  apply Tensor.SEqGetS.of.SEq.GtLength
  apply MatmulResizeS.as.Matmul.of.EqLengthS.GtLength_0 h h_length


-- created on 2026-07-17
