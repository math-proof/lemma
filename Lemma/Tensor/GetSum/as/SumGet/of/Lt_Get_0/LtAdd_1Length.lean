import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.LengthSum.eq.Length.of.Gt_0
import Lemma.Tensor.Sum.as.Stack_Sum.of.LtAdd_1Length
import Lemma.Tensor.SEqGetS.of.SEq.Lt_Length
import Lemma.Tensor.EqGetStack.of.Lt
open Tensor


@[main]
private lemma main
  [Add α] [Zero α]
  {dim i : ℕ}
-- given
  (h_dim : dim + 1 < s.length)
  (h_i : i < s[0])
  (X : Tensor α s) :
-- imply
  have : i < X.length := by rwa [Length.eq.Get_0.of.GtLength_0]
  have : i < (X.sum (dim + 1)).length := by rwa [LengthSum.eq.Length.of.Gt_0 (by linarith)]
  (X.sum (dim + 1))[i] ≃ X[i].sum dim := by
-- proof
  intro h_i_length _
  have := Sum.as.Stack_Sum.of.LtAdd_1Length h_dim X
  have h_i' : i < (X.sum (dim + 1)).length := by
    rwa [LengthSum.eq.Length.of.Gt_0 (by linarith)]
  have := SEqGetS.of.SEq.Lt_Length h_i' this
  simp [EqGetStack.of.Lt h_i] at this
  assumption


-- created on 2025-06-24
-- updated on 2025-07-13
