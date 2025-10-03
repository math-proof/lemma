import Lemma.Algebra.Le_SubMulS.of.Lt
import Lemma.Algebra.EqMul_Div.of.Dvd
import Lemma.List.Get_0.dvd.Prod.of.GtLength_0
open Algebra List


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h : s.length > 0)
  (h_i : i < s[0]) :
-- imply
  s.prod / s[0] ≤ s.prod - i * (s.prod / s[0]) := by
-- proof
  convert Le_SubMulS.of.Lt h_i (s.prod / s[0])
  rw [EqMul_Div.of.Dvd]
  apply Get_0.dvd.Prod.of.GtLength_0 h


-- created on 2025-07-17
-- updated on 2025-07-18
