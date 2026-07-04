import Lemma.List.Drop.eq.ListGet.of.GtLength_0
import Lemma.List.EqAppendTake__ListGet.of.GeLength_2
import Lemma.List.EraseIdx.eq.Append_Drop_Add_1
import Lemma.List.EraseIdxAppend.eq.Append_EraseIdx.of.LeLength
import Lemma.Nat.EqAddMulDiv
import Lemma.Bool.SEq.is.EqCast.of.Eq
import sympy.tensor.tensor
open List Nat Bool


@[main, cast]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h_s : s.length ≥ 2)
  (h_n : n = s[s.length - 2])
  (X : Tensor α [n])
  (Y : Tensor α s) :
-- imply
  let batch_size := s.take (s.length - 2)
  let k := s[s.length - 1]
  let Y' : Tensor α (batch_size ++ [n, k]) := cast (by rwa [h_n, EqAppendTake__ListGet.of.GeLength_2]) Y
  let X' := X.broadcast (batch_size ++ [1, n]) (by simp)
  X.matmul Y ≃ (X'.batch_dot Y').select ⟨s.length - 2, by simp [batch_size]⟩ ⟨0, by grind⟩ := by
-- proof
  unfold Tensor.matmul
  apply SEq.of.Eq_Cast
  .
    split_ifs
    repeat grind
  .
    congr
    simp [Tensor.matmul_shape]
    simp [show s ≠ [] by grind]
    rw [EraseIdxAppend.eq.Append_EraseIdx.of.LeLength (by grind)]
    simp [EraseIdx.eq.Append_Drop_Add_1]
    simp [show s.length - 2 + 1 = s.length - 1 by omega]
    rw [Drop.eq.ListGet.of.GtLength_0 (by omega)]


-- created on 2026-01-07
