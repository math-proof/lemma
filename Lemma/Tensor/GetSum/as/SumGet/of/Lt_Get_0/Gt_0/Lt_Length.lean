import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.LengthSum.eq.Length.of.Gt_0
import Lemma.Tensor.GetSum.as.SumGet.of.Lt_Get_0.Add_1.lt.Length
open Tensor


@[main]
private lemma main
  [Add α] [Zero α]
  {dim i : ℕ}
-- given
  (h₀ : dim < s.length)
  (h₁ : dim > 0)
  (h₂ : i < s[0])
  (X : Tensor α s) :
-- imply
  let h_shape := LengthSum.eq.Length.of.Gt_0 h₁ X
  let h_i : i < X.length := by rwa [Length.eq.Get_0.of.GtLength_0]
  (X.sum dim)[i] ≃ X[i].sum (dim - 1) := by
-- proof
  intro h_shape h_i'
  cases dim with
  | zero =>
    contradiction
  | succ dim =>
    apply GetSum.as.SumGet.of.Lt_Get_0.Add_1.lt.Length (by linarith) (by assumption)


-- created on 2025-06-22
-- updated on 2025-07-01
