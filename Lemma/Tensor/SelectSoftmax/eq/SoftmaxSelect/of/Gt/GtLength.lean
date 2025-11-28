import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.List.EraseIdxEraseIdx.of.Gt.GtLength
import Lemma.Nat.EqDivS.of.Eq
import Lemma.Tensor.SelectDiv.eq.DivSelectS
import Lemma.Tensor.SelectExp.eq.ExpSelect
import Lemma.Tensor.SelectKeepdim.eq.KeepdimCast_Select.of.Gt.GtLength
import Lemma.Tensor.Softmax.eq.Div_SumExp
import Lemma.Tensor.Sum.eq.Sum_Select
open Bool List Nat Tensor


@[main, comm]
private lemma main
  [Exp α]
-- given
  (h_k : s.length > k)
  (h_d : k > d)
  (X : Tensor α s)
  (i : Fin s[d]) :
-- imply
  (X.softmax k).select ⟨d, by omega⟩ i = (X.select ⟨d, by omega⟩ i).softmax (k - 1) := by
-- proof
  repeat rw [Softmax.eq.Div_SumExp]
  rw [SelectDiv.eq.DivSelectS]
  rw [SelectExp.eq.ExpSelect]
  apply EqDivS.of.Eq.left
  rw [SelectKeepdim.eq.KeepdimCast_Select.of.Gt.GtLength (by omega) (by omega)]
  apply congrArg
  apply EqCast.of.SEq.Eq
  ·
    rw [EraseIdxEraseIdx.of.Gt.GtLength (by grind) h_d]
  ·
    rw [Sum.eq.Sum_Select (exp X) ⟨k, by grind⟩]
    rw [Sum.eq.Sum_Select (exp (X.select ⟨d, by omega⟩ i)) ⟨k - 1, by grind⟩]
    sorry


-- created on 2025-11-17
-- updated on 2025-11-27
