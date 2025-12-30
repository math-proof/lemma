import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.List.EraseIdxEraseIdx.of.Gt.GtLength
import Lemma.Nat.EqDivS.of.Eq
import Lemma.Tensor.SelectDiv.eq.DivSelectS
import Lemma.Tensor.SelectExp.eq.ExpSelect
import Lemma.Tensor.SelectKeepdim.eq.KeepdimCast_Select.of.Gt
import Lemma.Tensor.SelectSum.eq.SumSelect.of.Gt
import Lemma.Tensor.Softmax.eq.DivExp_KeepdimSumExp
import Lemma.Tensor.Softmax.eq.One.of.LeLength
open Bool List Nat Tensor


@[main, comm]
private lemma main
  [Exp α]
  {d : Fin s.length}
  {k : ℕ}
-- given
  (h_d : k > d)
  (X : Tensor α s)
  (i : Fin s[d]) :
-- imply
  (X.softmax k).select ⟨d, by omega⟩ i = (X.select ⟨d, by omega⟩ i).softmax (k - 1) := by
-- proof
  repeat rw [Softmax.eq.DivExp_KeepdimSumExp]
  rw [SelectDiv.eq.DivSelectS]
  rw [SelectExp.eq.ExpSelect]
  apply EqDivS.of.Eq.left
  rw [SelectKeepdim.eq.KeepdimCast_Select.of.Gt h_d]
  apply congrArg
  apply EqCast.of.SEq.Eq
  ·
    rw [EraseIdxEraseIdx.of.Gt.GtLength (by grind) h_d]
  ·
    have := SelectSum.eq.SumSelect.of.Gt h_d (exp X) i
    apply SEq.trans this
    rw [SelectExp.eq.ExpSelect]


-- created on 2025-11-17
-- updated on 2025-11-28
