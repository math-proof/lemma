import Lemma.Tensor.Mul
import Instance.Data.Holor.Tensor.Part2
open Tensor


@[path]
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
