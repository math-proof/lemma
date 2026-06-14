import Lemma.List.Drop.eq.ListGet.of.GtLength_0
import Lemma.List.Drop.eq.ListGetS.of.GeLength_2
import Lemma.List.EqAppendS.of.Eq
import Lemma.List.EqAppendTake__Drop
import Lemma.List.EraseIdx.eq.Append_Drop_Add_1
import Lemma.List.EraseIdxAppend.eq.Append_EraseIdx.of.LeLength
import Lemma.Nat.EqAddMulDiv
import sympy.tensor.tensor
open List Nat


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h_s' : s'.length ≥ 2)
  (h_n : n < s'[s'.length - 2])
  (X : Tensor α [n])
  (Y : Tensor α s') :
-- imply
  X.matmul Y =
    let batch_size' := s'.take (s'.length - 2)
    let n' := s'[s'.length - 2]
    let k' := s'[s'.length - 1]
    let Y : Tensor α (batch_size' ++ [n', k']) := cast
      (by
        congr
        simp [batch_size', n', k']
        conv_lhs => rw [← EqAppendTake__Drop s' (s'.length - 2)]
        apply EqAppendS.of.Eq.left
        apply Drop.eq.ListGetS.of.GeLength_2 h_s'
      )
      Y
    let q := n' / n
    let r := n' % n
    let X : Tensor α [n'] := cast
      (by simp [q, r, EqAddMulDiv])
      ((cast (by grind) (X.repeat q ⟨0, by simp⟩) : Tensor α [q * n]) ++ (0 : Tensor α [r]))
    let X := X.broadcast ((batch_size' ++ [1, n'])) (by simp)
    cast
      (by
        congr
        simp [batch_size', k', Tensor.matmul_shape]
        have h_s' : s' ≠ [] := by grind
        simp [h_s']
        rw [EraseIdxAppend.eq.Append_EraseIdx.of.LeLength (by grind)]
        simp [EraseIdx.eq.Append_Drop_Add_1]
        simp [show s'.length - 2 + 1 = s'.length - 1 by omega]
        rw [Drop.eq.ListGet.of.GtLength_0 (by omega)]
      )
      ((X.batch_dot Y).select ⟨s'.length - 2, by simp [batch_size']⟩ ⟨0, by grind⟩) := by
-- proof
  unfold Tensor.matmul
  split_ifs
  repeat grind


-- created on 2026-01-07
