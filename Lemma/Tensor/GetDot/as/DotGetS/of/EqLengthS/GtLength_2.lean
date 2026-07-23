import Lemma.Bool.SEq.is.Eq
import Lemma.List.EqCons_Tail.of.GtLength
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetEinsum.as.EinsumGetS.of.EqLengthS.GtLength_2
import Lemma.Tensor.GtLengthEinsum.of.GeLengthS.GeLength_2
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
open Bool List Tensor
set_option maxHeartbeats 1000000


@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
  {s s' : List ℕ}
-- given
  (h_s : s.length > 2)
  (h_slen : s'.length = s.length)
  (X : Tensor α s)
  (Y : Tensor α s')
  (i : Fin (s[0] ⊓ s'[0])) :
-- imply
  (X @ Y)[i]'(by simpa [Dot.dot] using GtLengthEinsum.of.GeLengthS.GeLength_2 (by omega) (by omega) X Y ⟨i, by grind⟩) ≃ X[i]'(by rw [Length.eq.Get_0.of.GtLength_0 (by omega)]; grind) @ Y[i]'(by rw [Length.eq.Get_0.of.GtLength_0 (by omega)]; grind) := by
-- proof
  have h_X : s = s[0] :: s.tail := (EqCons_Tail.of.GtLength h_s).symm
  have h_Y : s' = s'[0] :: s'.tail := (EqCons_Tail.of.GtLength (h_slen ▸ h_s)).symm
  let X' := cast (congrArg (Tensor α) h_X) X
  let Y' := cast (congrArg (Tensor α) h_Y) Y
  have h_einsum := GetEinsum.as.EinsumGetS.of.EqLengthS.GtLength_2 h_s h_slen.symm X Y i
  simp only [GetElem.getElem, Dot.dot]
  apply h_einsum.trans
  have hX := GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin (by grind) h_X X ⟨i, by grind⟩
  have hY := GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin (by grind) h_Y Y ⟨i, by grind⟩
  apply SEq.of.Eq
  simp only [GetElem.getElem, hX, hY]
  grind


-- created on 2026-01-04
-- updated on 2026-07-20
