import Lemma.Tensor.Length.eq.Get_0.of.GtLength
open Tensor


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h : s.length > j)
  (X : Tensor α s)
  (i : Fin s[0]) :
-- imply
  i < X.length := by
-- proof
  rw [Length.eq.Get_0.of.GtLength h]
  simp


-- created on 2025-11-06
