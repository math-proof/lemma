import Lemma.Nat.EqAddMulDiv
import sympy.tensor.tensor
open Nat


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h : n > n')
  (X : Tensor α [n])
  (Y : Tensor α [n']) :
-- imply
  X.matmul Y =
    let q := n / n'
    let r := n % n'
    let Y : Tensor α [n] := cast
      (by simp [q, r, EqAddMulDiv])
      ((cast (by simp_all) (Y.repeat q ⟨0, by simp⟩) : Tensor α [q * n']) ++ (0 : Tensor α [r]))
    ((X.data * Y.data).sum : Tensor α []) := by
-- proof
  unfold Tensor.matmul
  split_ifs
  repeat grind


-- created on 2026-01-05
