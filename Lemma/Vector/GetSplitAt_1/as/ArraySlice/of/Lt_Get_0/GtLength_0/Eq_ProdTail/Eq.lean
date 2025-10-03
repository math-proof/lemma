import Lemma.Algebra.ProdTake_1.eq.Get_0.of.GtLength_0
import Lemma.Vector.ArraySlice.as.GetSplitAt_1.of.Lt_Get_0.GtLength_0.Eq_ProdTail
open Algebra Vector


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h_eq_i : i = i')
  (h_n : n = s.tail.prod)
  (h_s : s.length > 0)
  (h_i : i < s[0])
  (v : List.Vector α s.prod) :
-- imply
  have : i < (s.take 1).prod := by rwa [ProdTake_1.eq.Get_0.of.GtLength_0 h_s]
  (v.splitAt 1)[i] ≃ v.array_slice (i' * n) n := by
-- proof
  rw [← h_eq_i]
  apply GetSplitAt_1.as.ArraySlice.of.Lt_Get_0.GtLength_0.Eq_ProdTail h_n h_s h_i


-- created on 2025-07-15
