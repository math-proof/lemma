import Lemma.List.Drop.eq.ListGetS.of.GeLength_2
import Lemma.List.EqAppendS.of.Eq
import Lemma.List.EqAppendTake__Drop
import Lemma.Nat.EqAddMulDiv
import sympy.tensor.tensor
open List Nat


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h_s : s.length ≥ 2)
  (h_s' : s'.length ≥ 2)
  (h_n : s[s.length - 1] < s'[s'.length - 2])
  (X : Tensor α s)
  (Y : Tensor α s') :
-- imply
  X.matmul Y =
    let batch_size := s.take (s.length - 2)
    let batch_size' := s'.take (s'.length - 2)
    let m := s[s.length - 2]
    let n := s[s.length - 1]
    let n' := s'[s'.length - 2]
    let k := s'[s'.length - 1]
    let X : Tensor α (batch_size ++ [m, n]) := cast
      (by
        congr
        simp [batch_size, m, n]
        conv_lhs => rw [← EqAppendTake__Drop s (s.length - 2)]
        apply EqAppendS.of.Eq.left
        apply Drop.eq.ListGetS.of.GeLength_2 h_s
      )
      X
    let Y : Tensor α (batch_size' ++ [n', k]) := cast
      (by
        congr
        simp [batch_size', n', k]
        conv_lhs => rw [← EqAppendTake__Drop s' (s'.length - 2)]
        apply EqAppendS.of.Eq.left
        apply Drop.eq.ListGetS.of.GeLength_2 h_s'
      )
      Y
    let q := n' / n
    let r := n' % n
    let X : Tensor α (batch_size ++ [m, n']) := cast
      (by simp [q, r, EqAddMulDiv])
      ((cast (by simp; grind) (X.repeat q ⟨s.length - 1, by simp [batch_size]; omega⟩) : Tensor α (batch_size ++ [m] ++ [q * n])) ++ (0 : Tensor α (batch_size ++ [m] ++ [r])))
    cast
      (by
        congr
        simp [batch_size, batch_size', m, k, Tensor.matmul_shape, Tensor.broadcast_shape]
        grind
      )
      (Tensor.broadcast_matmul X Y) := by
-- proof
  unfold Tensor.matmul
  split_ifs
  repeat grind


-- created on 2026-01-10
