import Lemma.Tensor.DataMul.eq.MulData
import Lemma.Tensor.DataNeg.eq.NegData
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.NegMul.eq.MulNeg
import sympy.tensor.tensor
open Tensor Vector


@[main, comm]
private lemma main
  [Mul α] [HasDistribNeg α]
-- given
  (X : Tensor α s)
  (a : α) :
-- imply
  -(X * a) = -X * a := by
-- proof
  apply Eq.of.EqDataS
  rw [DataNeg.eq.NegData]
  rw [DataMul.eq.MulData]
  rw [NegMul.eq.MulNeg]
  rw [DataMul.eq.MulData]
  rw [DataNeg.eq.NegData]


-- created on 2026-01-02
