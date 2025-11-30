import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.SEqGetS.of.SEq.GtLength
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.LengthUnsqueeze.eq.Length.of.Gt_0
import Lemma.Tensor.Unsqueeze.as.Stack_Unsqueeze.of.GtLength_0
open Tensor


@[main]
private lemma main
  {i : ℕ}
-- given
  (h_s : s.length > 0)
  (h_i : i < s[0])
  (X : Tensor α s)
  (d : ℕ) :
-- imply
  have : i < X.length := by rwa [Length.eq.Get_0.of.GtLength_0]
  have : i < (X.unsqueeze (d + 1)).length := by rwa [LengthUnsqueeze.eq.Length.of.Gt_0 (by linarith)]
  (X.unsqueeze (d + 1))[i] ≃ X[i].unsqueeze d := by
-- proof
  intro h_i_length h_i'
  have := Unsqueeze.as.Stack_Unsqueeze.of.GtLength_0 h_s X d
  have := SEqGetS.of.SEq.GtLength.fin h_i' this
  rwa [EqGetStack.fn.fin] at this


-- created on 2025-07-13
