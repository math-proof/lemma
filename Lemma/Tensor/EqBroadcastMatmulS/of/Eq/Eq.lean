import sympy.Basic
import sympy.tensor.tensor


@[main]
private lemma main
  [Mul α] [Zero α] [Add α]
  {A : Tensor α (s ++ [m, n])}
  {B : Tensor α (s' ++ [n, k])}
-- given
  (h_A : A = A')
  (h_B : B = B') :
-- imply
  A.broadcast_matmul B = A'.broadcast_matmul B' := by
-- proof
  rw [h_A, h_B]


-- created on 2026-01-13
