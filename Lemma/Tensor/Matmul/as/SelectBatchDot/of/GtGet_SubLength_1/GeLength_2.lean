import Lemma.List.Drop.eq.ListGetS.of.GeLength_2
import Lemma.List.DropLast.eq.Take_SubLength_1
import Lemma.List.EqAppendS.of.Eq
import Lemma.List.EqAppendTake__Drop
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
  (h_s' : s[s.length - 1] > n')
  (X : Tensor α s)
  (Y : Tensor α [n']) :
-- imply
  let batch_size := s.take (s.length - 2)
  let k := s[s.length - 2]
  let n := s[s.length - 1]
  let X' : Tensor α (batch_size ++ [k, n]) := cast
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
  let Y' : Tensor α [n] := cast
    (by simp [q, r, EqAddMulDiv])
    ((cast (by grind) (Y.repeat q ⟨0, by simp⟩) : Tensor α [q * n']) ++ (0 : Tensor α [r]))
  let Y' := Y'.broadcast ((batch_size ++ [n, 1])) (by simp)
  X.matmul Y ≃ (X'.batch_dot Y').select ⟨s.length - 1, by simp [batch_size]; omega⟩ ⟨0, by grind⟩ := by
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
    simp [show s.length ≠ 1 by grind]
    rw [EraseIdxAppend.eq.Append_EraseIdx.of.LeLength (by grind)]
    simp [EraseIdx.eq.Append_Drop_Add_1]
    simp [show s.length - 1 - (s.length - 2) = 1 by omega]
    simp [show s.length - 2 + 1 = s.length - 1 by omega]
    rw [DropLast.eq.Take_SubLength_1]


-- created on 2026-01-10
