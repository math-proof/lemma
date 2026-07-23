import Lemma.List.EqCons_Tail.of.GtLength_0
import Lemma.Tensor.EqGetS.of.Eq.GtLength_0
import Lemma.Tensor.GetMatmul.as.MatmulGetS.of.EqLengthS.GtLength_0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.Tensordot.eq.Matmul.of.EqLengthS
open List Tensor
set_option maxHeartbeats 1000000


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
  have h_i : i < (X.tensordot Y).length := by
    rw [Tensordot.eq.Matmul.of.EqLengthS h_len]
    rw [Length.eq.Get_0.of.GtLength_0 (by grind)]
    simp [broadcast_shape]
    grind
  have : i < s[0] := by grind
  have : i < s'[0] := by grind
  (X.tensordot Y)[i]'h_i ≃ X'[i].tensordot Y'[i] := by
-- proof
  intros h_X h_Y X' Y' h_i
  simp only [GetElem.getElem]
  have h_tensordot := Tensordot.eq.Matmul.of.EqLengthS h_len X Y
  rw [EqGetS.of.Eq.GtLength_0 (by grind) h_tensordot ⟨i, by simp [broadcast_shape]; grind⟩]
  rw [Tensordot.eq.Matmul.of.EqLengthS (by grind) (X'.get ⟨i, by grind⟩) (Y'.get ⟨i, by grind⟩)]
  apply GetMatmul.as.MatmulGetS.of.EqLengthS.GtLength_0.fin h_s h_len


-- created on 2026-07-20
