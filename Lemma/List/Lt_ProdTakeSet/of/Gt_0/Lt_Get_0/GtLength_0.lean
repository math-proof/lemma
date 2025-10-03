import Lemma.List.ProdTake_1.eq.Get_0.of.GtLength_0
import Lemma.List.LengthSet.eq.Length
import Lemma.List.GetSet.eq.Get_0.of.Gt_0.GtLength_0
open List


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h_s : s.length > 0)
  (h_i : i < s[0])
  (h_d : d > 0)
  (x : ℕ) :
-- imply
  i < ((s.set d x).take 1).prod := by
-- proof
  rw [ProdTake_1.eq.Get_0.of.GtLength_0]
  rw [GetSet.eq.Get_0.of.Gt_0.GtLength_0]
  repeat assumption


-- created on 2025-07-17
