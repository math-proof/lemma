import Lemma.List.ProdDrop_1.eq.MinProdTail.of.Lt_Get_0.GtLength_0
import Lemma.Bool.EqCast.of.SEq
import Lemma.List.ProdTake_1.eq.Get_0.of.GtLength_0
import Lemma.Vector.ArraySlice.as.GetSplitAt_1.of.Lt_Get_0.GtLength_0.Eq_ProdTail
open Vector List Bool


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h_n : n = s.tail.prod)
  (h_s : s.length > 0)
  (h_i : i < s[0])
  (v : List.Vector α s.prod) :
-- imply
  have h_prod : (s.drop 1).prod = n ⊓ (s.prod - i * n) := by
    rw [h_n]
    apply ProdDrop_1.eq.MinProdTail.of.Lt_Get_0.GtLength_0 h_s h_i
  have : i < (s.take 1).prod := by rwa [ProdTake_1.eq.Get_0.of.GtLength_0 h_s]
  v.array_slice (i * n) n = cast (by rw [h_prod]) (v.splitAt 1)[i] := by
-- proof
  apply Eq_Cast.of.SEq
  apply ArraySlice.as.GetSplitAt_1.of.Lt_Get_0.GtLength_0.Eq_ProdTail
  repeat assumption


-- created on 2025-07-12
