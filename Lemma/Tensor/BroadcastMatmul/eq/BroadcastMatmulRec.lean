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
  X.tensordot Y = X.matmul Y (by grind) := by
-- proof
  unfold Tensor.tensordot
  simp


-- created on 2026-01-11
