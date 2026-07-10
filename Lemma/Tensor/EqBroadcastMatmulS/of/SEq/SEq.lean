import Lemma.Bool.HEq.of.SEq
import sympy.Basic
import sympy.tensor.tensor
open Bool


@[main]
private lemma main
  [Mul α] [Zero α] [Add α]
  {A : Tensor α (s ++ [m, n])}
  {A' : Tensor α (s ++ [m, n'])}
  {B : Tensor α (s' ++ [n, k])}
  {B' : Tensor α (s' ++ [n', k])}
-- given
  (h_A : A ≃ A')
  (h_B : B ≃ B') :
-- imply
  A.tensordot B = A'.tensordot B' := by
-- proof
  congr 1
  .
    have h_A := h_A.left
    simp_all
  .
    apply HEq.of.SEq h_A
  .
    apply HEq.of.SEq h_B


-- created on 2026-07-10
