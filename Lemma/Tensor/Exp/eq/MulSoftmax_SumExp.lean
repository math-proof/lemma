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
  exp X = X.softmax 0 * (let s : Tensor α [] := (exp X).sum 0; s) := by
-- proof
  conv_lhs => rw [Exp.eq.MulSoftmax_KeepdimSumExp X 0]
  rw [Mul_Keepdim.eq.Mul]


-- created on 2021-12-14
