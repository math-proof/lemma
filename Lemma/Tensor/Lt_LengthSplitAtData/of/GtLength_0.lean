import Lemma.List.ProdTake_1.eq.Get_0.of.GtLength_0
import sympy.tensor.Basic
open List


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h : s.length > 0)
  (X : Tensor α s)
  (i : Fin s[0]) :
-- imply
  i < (X.data.splitAt 1).length := by
-- proof
  simp [List.Vector.length]
  simp [ProdTake_1.eq.Get_0.of.GtLength_0 h]


-- created on 2025-11-01
