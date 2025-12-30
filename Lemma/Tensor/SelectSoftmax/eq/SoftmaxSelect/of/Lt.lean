import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.List.EraseIdxEraseIdx.of.Gt.GtLength
import Lemma.Nat.EqDivS.of.Eq
import Lemma.Tensor.SelectDiv.eq.DivSelectS
import Lemma.Tensor.SelectExp.eq.ExpSelect
import Lemma.Tensor.SelectKeepdim.eq.KeepdimCast_Select.of.Lt
import Lemma.Tensor.SelectSum.eq.SumSelect.of.Lt
import Lemma.Tensor.Softmax.eq.DivExp_KeepdimSumExp
open Bool List Nat Tensor


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
  repeat rw [Softmax.eq.DivExp_KeepdimSumExp]
  rw [SelectDiv.eq.DivSelectS]
  rw [SelectExp.eq.ExpSelect]
  apply EqDivS.of.Eq.left
  rw [SelectKeepdim.eq.KeepdimCast_Select.of.Lt h_k]
  apply congrArg
  apply EqCast.of.SEq.Eq
  ·
    conv_rhs => rw [EraseIdxEraseIdx.of.Gt.GtLength (by grind) h_k]
  ·
    have := SelectSum.eq.SumSelect.of.Lt h_k (exp X) i
    apply SEq.trans this
    rw [SelectExp.eq.ExpSelect]


-- created on 2025-11-17
-- updated on 2025-11-28
