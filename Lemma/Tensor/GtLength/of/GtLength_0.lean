import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
open Tensor


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h : s.length > 0)
  (X : Tensor α s)
  (i : Fin s[0]) :
-- imply
  i < X.length := by
-- proof
  rw [Length.eq.Get_0.of.GtLength_0 h]
  simp


-- created on 2025-11-01
