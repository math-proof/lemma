import Lemma.List.ProdTake_1.eq.Get_0.of.GtLength_0
import Lemma.List.ProdDrop_1.eq.MinProdTail.of.Lt_Get_0.GtLength_0
import Lemma.Vector.ArraySlice.as.GetCast_SplitAt_1.of.Lt_Get_0.GtLength_0.Eq_ProdTail.Eq_Prod
import Lemma.Logic.EqCast.of.SEq
open Logic Vector List


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h_m : m = s.prod)
  (h_n : n = s.tail.prod)
  (h_s : s.length > 0)
  (h_i : i < s[0])
  (v : List.Vector α m) :
-- imply
  have h : List.Vector α m = List.Vector α s.prod := by rw [h_m]
  have : i < (s.take 1).prod := by rwa [ProdTake_1.eq.Get_0.of.GtLength_0 h_s]
  have h_prod : (s.drop 1).prod = n ⊓ (m - i * n) := by
    rw [h_n, h_m]
    apply ProdDrop_1.eq.MinProdTail.of.Lt_Get_0.GtLength_0 h_s h_i
  v.array_slice (i * n) n = cast (by rw [h_prod]) ((cast h v).splitAt 1)[i] := by
-- proof
  apply Eq_Cast.of.SEq
  apply ArraySlice.as.GetCast_SplitAt_1.of.Lt_Get_0.GtLength_0.Eq_ProdTail.Eq_Prod
  repeat assumption


-- created on 2025-07-11
