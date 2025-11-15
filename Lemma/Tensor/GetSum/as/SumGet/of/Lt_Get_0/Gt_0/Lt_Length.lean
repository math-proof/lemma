import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.LengthSum.eq.Length.of.Gt_0
import Lemma.Tensor.GetSum.as.SumGet.of.Lt_Get_0.LtAdd_1Length
open Tensor


@[main]
private lemma main
  [Add α] [Zero α]
  {d i : ℕ}
-- given
  (h_s : d < s.length)
  (h_d : d > 0)
  (h_i : i < s[0])
  (X : Tensor α s) :
-- imply
  let h_shape := LengthSum.eq.Length.of.Gt_0 h_d X
  let h_i : i < X.length := by rwa [Length.eq.Get_0.of.GtLength_0]
  (X.sum d)[i] ≃ X[i].sum (d - 1) := by
-- proof
  intro h_shape h_i'
  cases d with
  | zero =>
    contradiction
  | succ d =>
    apply GetSum.as.SumGet.of.Lt_Get_0.LtAdd_1Length h_s h_i


@[main]
private lemma fin
  [Add α] [Zero α]
  {d i : ℕ}
-- given
  (h_s : d < s.length)
  (h_d : d > 0)
  (h_i : i < s[0])
  (X : Tensor α s) :
-- imply
  have h_shape := LengthSum.eq.Length.of.Gt_0 h_d X
  have h_i : i < X.length := by rwa [Length.eq.Get_0.of.GtLength_0]
  (X.sum d).get ⟨i, by simp_all⟩ ≃ (X.get ⟨i, h_i⟩).sum (d - 1) := by
-- proof
  apply main h_s h_d h_i X


-- created on 2025-06-22
-- updated on 2025-07-01
