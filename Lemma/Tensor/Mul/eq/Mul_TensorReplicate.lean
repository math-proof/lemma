import Lemma.Tensor.DataMul.eq.MulData
import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.Mul.eq.Mul_Replicate
open Tensor Vector


@[main, comm]
private lemma main
  [Mul α]
-- given
  (X : Tensor α s)
  (a : α) :
-- imply
  X * a = X * ⟨List.Vector.replicate s.prod a⟩ := by
-- proof
  apply Eq.of.EqDataS
  rw [DataMul.eq.MulData]
  rw [DataMul.eq.MulDataS]
  simp
  apply Mul.eq.Mul_Replicate


-- created on 2025-12-01
