import sympy.Basic
import sympy.tensor.tensor


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
  {s : List ℕ}
-- given
  (X : Tensor α (s ++ [m, n]))
  (Y : Tensor α (s ++ [n, k])) :
-- imply
  X.broadcast_matmul Y = X.broadcast_matmul_rec Y (by grind) := by
-- proof
  unfold Tensor.broadcast_matmul
  simp


-- created on 2026-01-11
