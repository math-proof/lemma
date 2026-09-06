import Lemma.Tensor.Mul
import sympy.tensor.tensor
open Tensor


@[main]
private lemma main
  [Semigroup α]
-- given
  (X Y Z : Tensor α []) :
-- imply
  X * Y * Z = X * (Y * Z) := by
-- proof
  simp only [Tensor.Mul]
  exact mul_assoc X Y Z


-- created on 2026-09-06
