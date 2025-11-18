import Lemma.Nat.EqDivS.of.Eq
import Lemma.Tensor.SelectDiv.eq.DivSelectS
import Lemma.Tensor.SelectExp.eq.ExpSelect
import Lemma.Tensor.Softmax.eq.Div_SumExp
import Lemma.Tensor.Sum.eq.SelectKeepdimSum
import sympy.tensor.functions
open Nat Tensor


@[main, comm]
private lemma main
  [Exp α]
  {d : Fin s.length}
  {k : ℕ}
-- given
  (h_k : k < d)
  (X : Tensor α s)
  (i : Fin s[d]) :
-- imply
  (X.softmax k).select d i = (X.select d i).softmax k := by
-- proof
  repeat rw [Softmax.eq.Div_SumExp]
  rw [SelectDiv.eq.DivSelectS]
  rw [SelectExp.eq.ExpSelect]
  apply EqDivS.of.Eq.left
  have := SelectKeepdimSum.eq.Sum (exp X) i
  -- rw [SelectKeepdimSum.eq.Sum]
  sorry


-- created on 2025-11-17
