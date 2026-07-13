import Lemma.Bool.SEq.is.Eq
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.LengthSoftmax.eq.Length
import Lemma.Tensor.SEqGetS.of.SEq.GtLength
import Lemma.Tensor.Softmax.as.Stack_Softmax.of.LtAdd_1Length
open Tensor Bool


@[main]
private lemma main
  [Exp α]
  {d i : ℕ}
-- given
  (h_d : d + 1 < s.length)
  (h_i : i < s[0])
  (X : Tensor α s) :
-- imply
  have : i < X.length := by rwa [Length.eq.Get_0.of.GtLength_0]
  have : i < (X.softmax (d + 1)).length := by
    rwa [LengthSoftmax.eq.Length]
  (X.softmax (d + 1))[i] = X[i].softmax d := by
-- proof
  intro h_i_length h_i'
  apply Eq.of.SEq
  have := Softmax.as.Stack_Softmax.of.LtAdd_1Length h_d X
  have := SEqGetS.of.SEq.GtLength.fin h_i' this
  rwa [EqGetStack.fn.fin] at this


-- created on 2025-11-30
