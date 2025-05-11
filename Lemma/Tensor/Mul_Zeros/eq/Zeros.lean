import sympy.tensor.tensor
import Lemma.Tensor.Mul.eq.Prod
import Lemma.Algebra.ZipWithHMul.eq.Replicate_0.of.Ge
import Lemma.Algebra.Ge.of.Eq
open Tensor Algebra


@[main]
private lemma main
  [MulZeroClass α]
  {a : Tensor α s} :
-- imply
  a * Zeros s = Zeros s := by
-- proof
  rw [Mul.eq.Prod]
  congr
  simp [Zeros]
  have h_Eq : a.data.val.length = s.prod := by simp
  have h_Ge := Ge.of.Eq h_Eq
  rw [ZipWithHMul.eq.Replicate_0.of.Ge h_Ge]


-- created on 2025-05-02
