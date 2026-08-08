import sympy.Basic
import sympy.tensor.tensor
open Nat Tensor Vector


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (A B : Tensor α [n]) :
-- imply
  A @ B = (A.data @ B.data : Tensor α []) := by
-- proof
  sorry


-- created on 2026-08-08
