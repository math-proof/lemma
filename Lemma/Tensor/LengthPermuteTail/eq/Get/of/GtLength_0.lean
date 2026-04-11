import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
open List Tensor


@[main]
private lemma main
-- given
  (h : s.length > 0)
  (X : Tensor α s) :
-- imply
  (X.permuteTail s.length).length = s[s.length - 1] := by
-- proof
  rw [Length.eq.Get_0.of.GtLength_0]
  ·
    simp [List.rotate]
    grind
  ·
    simp
    omega


-- created on 2026-04-08
