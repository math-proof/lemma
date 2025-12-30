import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.LengthUnsqueeze.eq.Length.of.Gt_0
import Lemma.Tensor.GetUnsqueeze.as.UnsqueezeGet.of.Lt_Get_0.Gt_0.GtLength_0
import Lemma.Bool.EqCast.of.SEq
import Lemma.List.TailInsertIdx.eq.InsertIdxTail.of.Gt_0.GtLength_0
open Tensor List Bool


@[main]
private lemma main
-- given
  (h_s : s.length > 0)
  (h_d : d > 0)
  (h_i : i < s[0])
  (X : Tensor α s) :
-- imply
  have : i < X.length := by rwa [Length.eq.Get_0.of.GtLength_0 h_s]
  have : i < (X.unsqueeze d).length := by rwa [LengthUnsqueeze.eq.Length.of.Gt_0 h_d]
  (X.unsqueeze d)[i] = cast (by rwa [TailInsertIdx.eq.InsertIdxTail.of.Gt_0.GtLength_0 h_s]) (X[i].unsqueeze (d - 1)) := by
-- proof
  have := GetUnsqueeze.as.UnsqueezeGet.of.Lt_Get_0.Gt_0.GtLength_0 h_s h_d h_i X
  apply Eq_Cast.of.SEq this


@[main]
private lemma fin
-- given
  (h_s : s.length > 0)
  (h_d : d > 0)
  (h_i : i < s[0])
  (X : Tensor α s) :
-- imply
  have h_Xi: i < X.length := by rwa [Length.eq.Get_0.of.GtLength_0 h_s]
  have hi : i < (X.unsqueeze d).length := by rwa [LengthUnsqueeze.eq.Length.of.Gt_0 h_d]
  (X.unsqueeze d).get ⟨i, hi⟩ = cast (by rwa [TailInsertIdx.eq.InsertIdxTail.of.Gt_0.GtLength_0 h_s]) ((X.get ⟨i, h_Xi⟩).unsqueeze (d - 1)) :=
-- proof
  main h_s h_d h_i X


-- created on 2025-07-13
