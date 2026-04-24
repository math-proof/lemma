import sympy.tensor.tensor
open Tensor


@[main, comm]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (X : Tensor α [n]) :
-- imply
  (X.sum 0).data.head = X.data.sum := by
-- proof
  unfold Tensor.sum
  simp
  unfold List.Vector.splitAt
  simp
  sorry


-- created on 2026-04-24
