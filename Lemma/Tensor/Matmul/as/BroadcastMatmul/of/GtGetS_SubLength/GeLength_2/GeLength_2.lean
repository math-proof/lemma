import Lemma.List.EqAppendTake__ListGet.of.GeLength_2
import Lemma.Nat.EqAddMulDiv
import Lemma.Bool.SEq.is.EqCast.of.Eq
import sympy.tensor.tensor
open List Nat Bool


@[main, cast]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h_s : s.length ≥ 2)
  (h_s' : s'.length ≥ 2)
  (h_n : s[s.length - 1] > s'[s'.length - 2])
  (X : Tensor α s)
  (Y : Tensor α s') :
-- imply
  let batch_size := s.take (s.length - 2)
  let batch_size' := s'.take (s'.length - 2)
  let m := s[s.length - 2]
  let n := s[s.length - 1]
  let n' := s'[s'.length - 2]
  let k := s'[s'.length - 1]
  let X' : Tensor α (batch_size ++ [m, n]) := cast (by rwa [EqAppendTake__ListGet.of.GeLength_2]) X
  let Y' : Tensor α (batch_size' ++ [n', k]) := cast (by rwa [EqAppendTake__ListGet.of.GeLength_2]) Y
  let q := n / n'
  let r := n % n'
  let Y' : Tensor α (batch_size' ++ [n, k]) := cast
    (by simp [q, r, EqAddMulDiv])
    ((cast (by simp [batch_size']) (Y'.repeat ⟨s'.length - 2, by simp [batch_size']⟩ q) : Tensor α (batch_size' ++ [q * n', k])) ++ (0 : Tensor α (batch_size' ++ [r, k])))
  X.matmul Y ≃ Tensor.broadcast_matmul X' Y' := by
-- proof
  unfold Tensor.matmul
  apply SEq.of.Eq_Cast
  .
    split_ifs
    repeat grind
  .
    congr
    simp [Tensor.matmul_shape, Tensor.broadcast_shape]
    grind


-- created on 2026-01-10
