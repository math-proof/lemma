import sympy.tensor.tensor
import Lemma.Tensor.Mul.eq.Prod
import Lemma.Algebra.ZipWithHMul.eq.Replicate_0.of.Le
import Lemma.Algebra.Le.of.Eq
open Tensor Algebra


@[main]
private lemma main
  [MulZeroClass α]
  {a : Tensor α s} :
-- imply
  Zeros s * a = Zeros s := by
-- proof
  rw [Mul.eq.Prod]
  congr
  simp [Zeros]
  have h_Eq : s.prod = a.data.val.length := by simp
  have h_Le := Le.of.Eq h_Eq
  rw [ZipWithHMul.eq.Replicate_0.of.Le h_Le]


-- created on 2025-05-02
