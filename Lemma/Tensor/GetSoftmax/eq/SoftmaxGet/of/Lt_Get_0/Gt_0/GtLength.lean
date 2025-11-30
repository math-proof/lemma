import Lemma.Tensor.GetSoftmax.eq.SoftmaxGet.of.Lt_Get_0.LtAdd_1Length
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.LengthSoftmax.eq.Length
open Tensor


@[main]
private lemma main
  [Exp α]
  {d i : ℕ}
-- given
  (h_s : s.length > d)
  (h_d : d > 0)
  (h_i : i < s[0])
  (X : Tensor α s) :
-- imply
  let h_shape := LengthSoftmax.eq.Length X d
  let h_i : i < X.length := by rwa [Length.eq.Get_0.of.GtLength_0]
  (X.softmax d)[i] = X[i].softmax (d - 1) := by
-- proof
  intro h_shape h_i'
  cases d with
  | zero =>
    contradiction
  | succ d =>
    apply GetSoftmax.eq.SoftmaxGet.of.Lt_Get_0.LtAdd_1Length h_s h_i


@[main]
private lemma fin
  [Exp α]
  {d i : ℕ}
-- given
  (h_s : s.length > d)
  (h_d : d > 0)
  (h_i : i < s[0])
  (X : Tensor α s) :
-- imply
  have h_shape := LengthSoftmax.eq.Length X d
  have h_i : i < X.length := by rwa [Length.eq.Get_0.of.GtLength_0]
  (X.softmax d).get ⟨i, by simp_all⟩ = (X.get ⟨i, h_i⟩).softmax (d - 1) := by
-- proof
  apply main h_s h_d h_i X


-- created on 2025-10-08
-- created on 2025-11-30
