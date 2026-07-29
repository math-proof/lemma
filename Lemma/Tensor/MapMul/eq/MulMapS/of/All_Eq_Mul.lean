import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Vector.MapMul.eq.MulMapS.of.All_Eq_Mul
open Tensor Vector


@[main, comm]
private lemma main
  [Mul α]
  [Mul β]
  {f : α → β}
-- given
  (hf : ∀ a b, f (a * b) = f a * f b)
  (A B : Tensor α s) :
-- imply
  (A * B).map f = A.map f * B.map f := by
-- proof
  apply Eq.of.EqDataS
  simp [Tensor.map]
  rw [DataMul.eq.MulDataS]
  apply MapMul.eq.MulMapS.of.All_Eq_Mul hf


-- created on 2026-07-29
