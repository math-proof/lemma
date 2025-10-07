import Lemma.List.ProdTake_1.eq.Get_0.of.GtLength_0
import Lemma.Vector.EqFlattenSplitAt
import Lemma.Bool.SEq.of.SEq.SEq
import Lemma.Vector.GetSplitAt_1.as.ArraySlice.of.Lt_Get_0.GtLength_0
open Vector List Bool


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h_s : s.length > 0)
  (h_i : i < s[0])
  (v : List.Vector α s.prod)
  (d : ℕ) :
-- imply
  have : i < (s.take 1).prod := by rwa [ProdTake_1.eq.Get_0.of.GtLength_0 h_s]
  ((v.splitAt 1)[i].splitAt d).flatten ≃ v.array_slice (i * s.tail.prod) s.tail.prod := by
-- proof
  intro h_i
  have := EqFlattenSplitAt (v.splitAt 1)[i] d
  apply this.trans
  apply GetSplitAt_1.as.ArraySlice.of.Lt_Get_0.GtLength_0
  assumption


-- created on 2025-07-08
