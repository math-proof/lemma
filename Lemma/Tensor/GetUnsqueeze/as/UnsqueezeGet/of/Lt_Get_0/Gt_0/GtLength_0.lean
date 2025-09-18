import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.LengthUnsqueeze.eq.Length.of.Gt_0
import Lemma.Tensor.GetUnsqueeze.as.UnsqueezeGet.of.Lt_Get_0.GtLength_0
open Tensor


@[main]
private lemma main
-- given
  (h_s : s.length > 0)
  (h : d > 0)
  (h_i : i < s[0])
  (X : Tensor α s) :
-- imply
  have : i < X.length := by rwa [Length.eq.Get_0.of.GtLength_0 h_s]
  have : i < (X.unsqueeze d).length := by rwa [LengthUnsqueeze.eq.Length.of.Gt_0 h]
  (X.unsqueeze d)[i] ≃ X[i].unsqueeze (d - 1) := by
-- proof
  intro h_length
  cases d with
  | zero =>
    contradiction
  | succ d =>
    apply GetUnsqueeze.as.UnsqueezeGet.of.Lt_Get_0.GtLength_0 (by linarith) (by assumption)


-- created on 2025-07-12
-- updated on 2025-07-13
