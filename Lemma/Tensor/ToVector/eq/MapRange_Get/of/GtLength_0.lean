import Lemma.Vector.EqGetRange
import Lemma.List.HeadD.eq.Get_0.of.GtLength_0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.ToVector.eq.MapRange_Get
open Vector List Tensor


@[main]
private lemma main
-- given
  (h : s.length > 0)
  (X : Tensor α s) :
-- imply
  X.toVector = (List.Vector.range (s.headD 1)).map fun i : Fin (s.headD 1) => X.get ⟨i, by
    rw [Length.eq.Get_0.of.GtLength_0 h]
    rw [← HeadD.eq.Get_0.of.GtLength_0 h 1]
    apply i.isLt
  ⟩ := by
-- proof
  match s with
  | [] =>
    simp at h
  | x :: xs =>
    rw [ToVector.eq.MapRange_Get]
    congr


-- created on 2025-10-06
-- updated on 2025-10-07
