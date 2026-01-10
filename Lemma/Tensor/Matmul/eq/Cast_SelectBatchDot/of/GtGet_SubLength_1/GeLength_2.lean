import Lemma.List.Drop.eq.ListGetS.of.GeLength_2
import Lemma.List.DropLast.eq.Take_SubLength_1
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
  (h_s : s.length ≥ 2)
  (h_s' : s[s.length - 1] > n')
  (X : Tensor α s)
  (Y : Tensor α [n']) :
-- imply
  X.matmul Y =
    let batch_size := s.take (s.length - 2)
    let k := s[s.length - 2]
    let n := s[s.length - 1]
    let X : Tensor α (batch_size ++ [k, n]) := cast
      (by
        congr
        simp [batch_size, n, k]
        conv_lhs => rw [← EqAppendTake__Drop s (s.length - 2)]
        apply EqAppendS.of.Eq.left
        apply Drop.eq.ListGetS.of.GeLength_2 h_s
      )
      X
    let q := n / n'
    let r := n % n'
    let Y : Tensor α [n] := cast
      (by simp [q, r, EqAddMulDiv])
      ((cast (by grind) (Y.repeat q ⟨0, by simp⟩) : Tensor α [q * n']) ++ (0 : Tensor α [r]))
    let Y := Y.broadcast ((batch_size ++ [n, 1])) (by simp)
    cast
      (by
        congr
        simp [batch_size, k, Tensor.matmul_shape]
        have h_s : s ≠ [] := by grind
        simp [h_s]
        have h_s : s.length ≠ 1 := by grind
        simp [h_s]
        rw [EraseIdxAppend.eq.Append_EraseIdx.of.LeLength (by grind)]
        simp [EraseIdx.eq.Append_Drop_Add_1]
        simp [show s.length - 1 - (s.length - 2) = 1 by omega]
        simp [show s.length - 2 + 1 = s.length - 1 by omega]
        rw [DropLast.eq.Take_SubLength_1]
      )
      ((X.batch_dot Y).select ⟨s.length - 1, by simp [batch_size]; omega⟩ ⟨0, by grind⟩) := by
-- proof
  unfold Tensor.matmul
  split_ifs
  repeat grind


-- created on 2026-01-10
