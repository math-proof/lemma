import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.Eq.is.All_EqGetS
open Tensor Vector


@[main, comm]
private lemma main
  [Mul α] [Mul β]
  {f : α → β}
-- given
  (hf : ∀ a b, f (a * b) = f a * f b)
  (A : Tensor α s)
  (b : α) :
-- imply
  (A * b).map f = A.map f * f b := by
-- proof
  apply Eq.of.EqDataS
  apply Eq.of.All_EqGetS.fin
  intro i
  simp [Tensor.map, HMul.hMul]
  apply hf


-- created on 2026-08-17
