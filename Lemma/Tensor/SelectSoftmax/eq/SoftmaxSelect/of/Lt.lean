import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.Nat.EqDivS.of.Eq
import Lemma.Tensor.SelectDiv.eq.DivSelectS
import Lemma.Tensor.SelectExp.eq.ExpSelect
import Lemma.Tensor.SelectKeepdim.eq.KeepdimCast_Select.of.Lt.GtLength
import Lemma.Tensor.Softmax.eq.Div_SumExp
import Lemma.Tensor.Sum.eq.Sum_Select
open Tensor Nat Bool


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
  rw [SelectKeepdim.eq.KeepdimCast_Select.of.Lt.GtLength (by omega) (by omega)]
  apply congrArg
  apply EqCast.of.SEq.Eq
  .
    conv_rhs => rw [List.EraseIdxEraseIdx.of.Gt.GtLength (by grind) h_k]
  .
    rw [Sum.eq.Sum_Select (exp X) ⟨k, by grind⟩]
    rw [Sum.eq.Sum_Select (exp (X.select d i)) ⟨k, by grind⟩]
    sorry


-- created on 2025-11-17
-- updated on 2025-11-24
