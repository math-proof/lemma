import Lemma.Tensor.Softmax.eq.DivExp_KeepdimSumExp
open Tensor


@[main]
private lemma main
  [ExpPos α]
-- given
  (X : Tensor α s)
  (d : ℕ) :
-- imply
  exp X = X.softmax d * ((exp X).sum d).keepdim := by
-- proof
  rw [Softmax.eq.DivExp_KeepdimSumExp]
  sorry


-- created on 2025-12-30
