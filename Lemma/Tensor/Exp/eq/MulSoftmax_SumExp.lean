import Lemma.Tensor.Exp.eq.MulSoftmax_KeepdimSumExp
import Lemma.Tensor.Mul_Keepdim.eq.Mul
open Tensor


@[main]
private lemma main
  [ExpPos α]
  [IsOrderedCancelAddMonoid α]
-- given
  (X : Tensor α [n]) :
-- imply
  exp X = X.softmax * id (α := Tensor α []) (exp X).sum := by
-- proof
  conv_lhs => rw [Exp.eq.MulSoftmax_KeepdimSumExp X 0]
  simp [Mul_Keepdim.eq.Mul]
  rfl


-- created on 2021-12-14
-- updated on 2026-08-19
