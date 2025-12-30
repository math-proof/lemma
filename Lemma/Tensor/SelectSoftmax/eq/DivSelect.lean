import Lemma.Nat.EqDivS.of.Eq
import Lemma.Tensor.SelectDiv.eq.DivSelectS
import Lemma.Tensor.Softmax.eq.DivExp_KeepdimSumExp
import Lemma.Tensor.Sum.eq.SelectKeepdimSum
open Nat Tensor


@[main, comm]
private lemma main
  [Exp α]
-- given
  (X : Tensor α s)
  (d : Fin s.length)
  (i : Fin s[d]) :
-- imply
  (X.softmax d).select d i = (exp X).select d i / (exp X).sum d := by
-- proof
  rw [Softmax.eq.DivExp_KeepdimSumExp]
  rw [SelectDiv.eq.DivSelectS]
  apply EqDivS.of.Eq.left
  apply SelectKeepdimSum.eq.Sum


-- created on 2025-11-17
